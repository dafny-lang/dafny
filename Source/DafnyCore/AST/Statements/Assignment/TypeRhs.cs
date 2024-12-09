using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// A TypeRhs represents one of five things, each having to do with allocating something in the heap:
///  * new T[EE]
///    This allocates an array of objects of type T (where EE is a list of expression)
///  * new T[EE] (elementInit)
///    This is like the previous, but uses "elementInit" to initialize the elements of the new array.
///  * new T[E] [EE]
///    This is like the first one, but uses the elements displayed in the list EE as the initial
///    elements of the array.  Only a 1-dimensional array may be used in this case.  The size denoted
///    by E must equal the length of EE.
///  * new C
///    This allocates an object of type C
///  * new C.Init(EE)
///    This allocates an object of type C and then invokes the method/constructor Init on it
/// There are three ways to construct a TypeRhs syntactically:
///  * TypeRhs(T, EE, initExpr)
///      -- represents "new T[EE]" (with "elementInit" being "null") and "new T[EE] (elementInit)"
///  * TypeRhs(T, E, EE)
///      -- represents "new T[E] [EE]"
///  * TypeRhs(C)
///      -- represents new C
///  * TypeRhs(Path, EE)
///    Here, Path may either be of the form C.Init
///      -- represents new C.Init(EE)
///    or all of Path denotes a type
///      -- represents new C._ctor(EE), where _ctor is the anonymous constructor for class C
/// </summary>
public class TypeRhs : AssignmentRhs, ICloneable<TypeRhs> {
  /// <summary>
  /// If ArrayDimensions != null, then the TypeRhs represents "new EType[ArrayDimensions]",
  ///     ElementInit is non-null to represent "new EType[ArrayDimensions] (elementInit)",
  ///     InitDisplay is non-null to represent "new EType[ArrayDimensions] [InitDisplay]",
  ///     and Arguments, Path, and InitCall are all null.
  /// If ArrayDimensions == null && Arguments == null, then the TypeRhs represents "new EType"
  ///     and ElementInit, Path, and InitCall are all null.
  /// If Arguments != null, then the TypeRhs represents "new Path(Arguments)"
  ///     and EType and InitCall is filled in by resolution, and ArrayDimensions == null and ElementInit == null.
  /// If OptionalNameComponent == null and Arguments != null, then the TypeRHS has not been resolved yet;
  ///   resolution will either produce an error or will chop off the last part of "EType" and move it to
  ///   OptionalNameComponent, after which the case above applies.
  /// </summary>
  [FilledInDuringResolution] public Type EType;  // in the case of Arguments != null
  public readonly List<Expression> ArrayDimensions;
  public readonly Expression ElementInit;
  public readonly List<Expression> InitDisplay;
  public readonly ActualBindings/*?*/ Bindings;
  public List<Expression> Arguments {
    get {
      Contract.Requires(Bindings != null);
      return Bindings.Arguments;
    }
  }

  public TypeRhs Clone(Cloner cloner) {
    return new TypeRhs(cloner, this);
  }

  public TypeRhs(Cloner cloner, TypeRhs original)
    : base(cloner, original) {
    EType = cloner.CloneType(original.EType);
    if (original.ArrayDimensions != null) {
      if (original.InitDisplay != null) {
        Contract.Assert(original.ArrayDimensions.Count == 1);
        ArrayDimensions = new List<Expression> { cloner.CloneExpr(original.ArrayDimensions[0]) };
        InitDisplay = original.InitDisplay.ConvertAll(cloner.CloneExpr);
      } else {
        ArrayDimensions = original.ArrayDimensions.Select(cloner.CloneExpr).ToList();
        ElementInit = cloner.CloneExpr(original.ElementInit);
      }
    } else if (original.Bindings == null) {
    } else {
      Path = cloner.CloneType(original.Path);
      Bindings = new ActualBindings(cloner, original.Bindings);
    }

    if (cloner.CloneResolvedFields) {
      InitCall = cloner.CloneStmt(original.InitCall, false) as CallStmt;
      Type = cloner.CloneType(original.Type);
    }
  }

  public Type Path;
  [FilledInDuringResolution] public CallStmt InitCall;  // may be null (and is definitely null for arrays),
  [FilledInDuringResolution] public PreType PreType;
  [FilledInDuringResolution] public Type Type;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(EType != null || Bindings != null);
    Contract.Invariant(ElementInit == null || InitDisplay == null);
    Contract.Invariant(InitDisplay == null || ArrayDimensions.Count == 1);
    Contract.Invariant(ArrayDimensions == null || (Bindings == null && Path == null && InitCall == null && 1 <= ArrayDimensions.Count));
    Contract.Invariant(Bindings == null || (Path != null && ArrayDimensions == null && ElementInit == null && InitDisplay == null));
    Contract.Invariant(!(ArrayDimensions == null && Bindings == null) || (Path == null && InitCall == null && ElementInit == null && InitDisplay == null));
  }

  public TypeRhs(IOrigin tok, Type type, List<Expression> arrayDimensions, Expression elementInit)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(type != null);
    Contract.Requires(arrayDimensions != null && 1 <= arrayDimensions.Count);
    EType = type;
    ArrayDimensions = arrayDimensions;
    ElementInit = elementInit;
  }
  public TypeRhs(IOrigin tok, Type type, Expression dim, List<Expression> initDisplay)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(type != null);
    Contract.Requires(dim != null);
    Contract.Requires(initDisplay != null);
    EType = type;
    ArrayDimensions = new List<Expression> { dim };
    InitDisplay = initDisplay;
  }
  public TypeRhs(IOrigin tok, Type type)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(type != null);
    EType = type;
  }
  public TypeRhs(IOrigin tok, Type path, List<ActualBinding> arguments)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(path != null);
    Contract.Requires(arguments != null);
    Path = path;
    Bindings = new ActualBindings(arguments);
  }
  public override bool CanAffectPreviouslyKnownExpressions {
    get {
      if (InitCall != null) {
        foreach (var mod in InitCall.Method.Mod.Expressions) {
          if (!(mod.E is ThisExpr)) {
            return true;
          }
        }
      }
      return false;
    }
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      if (ArrayDimensions != null) {
        foreach (var e in ArrayDimensions) {
          yield return e;
        }
        if (ElementInit != null) {
          yield return ElementInit;
        }
        if (InitDisplay != null) {
          foreach (var e in InitDisplay) {
            yield return e;
          }
        }
      }

      if (Bindings != null && Arguments != null) {
        foreach (var e in Arguments) {
          yield return e;
        }
      }
    }
  }
  public override IEnumerable<Statement> SubStatements {
    get {
      if (InitCall != null) {
        yield return InitCall;
      }
    }
  }

  public IOrigin Start => Tok;

  public override IEnumerable<INode> Children {
    get {
      if (Type == null) {
        return PreResolveChildren;
      }

      if (ArrayDimensions == null) {
        if (InitCall != null) {
          return new[] { InitCall };
        }

        return EType.Nodes;
      }

      return EType.Nodes.Concat(SubExpressions).Concat<Node>(SubStatements);
    }
  }
  public override IEnumerable<INode> PreResolveChildren =>
    new[] { EType, Type, Path }.OfType<Node>()
      .Concat<Node>(ArrayDimensions ?? Enumerable.Empty<Node>())
      .Concat<Node>(ElementInit != null ? new[] { ElementInit } : Enumerable.Empty<Node>())
      .Concat<Node>(InitDisplay ?? Enumerable.Empty<Node>())
      .Concat<Node>((Bindings != null && Bindings.ArgumentBindings != null ?
                       Bindings.ArgumentBindings.Select(a => a.Actual) : null) ??
                    (Bindings != null ? Arguments : null) ??
                    Enumerable.Empty<Node>());

  public override IEnumerable<Statement> PreResolveSubStatements => Enumerable.Empty<Statement>();
}