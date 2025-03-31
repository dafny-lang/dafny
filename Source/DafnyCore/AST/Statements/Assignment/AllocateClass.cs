#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// When calling a named constructor, the name is stored in the UserDefinedType of the field Path
/// </summary>
public class AllocateClass : TypeRhs, ICloneable<AllocateClass> {
  /// <summary>
  /// Contains both the type being constructed, and if specified, the constructor name.
  /// It's surprising that the constructor name is specified through a Type
  /// An alternative would be to let this field be an Expression
  /// And have a field "string? constructorName" that is set during resolution.
  /// </summary>
  public Type Path;
  public readonly ActualBindings? Bindings;

  [FilledInDuringResolution] public CallStmt? InitCall;  // may be null

  [SyntaxConstructor]
  public AllocateClass(IOrigin origin, Type path, ActualBindings? bindings, Attributes? attributes = null)
    : base(origin, attributes) {
    Path = path;
    Bindings = bindings;
  }

  public AllocateClass(IOrigin origin, Type path)
    : this(origin, path, null, null) {
  }

  public AllocateClass(IOrigin origin, Type path, List<ActualBinding> arguments)
    : this(origin, path, new ActualBindings(arguments)) {
  }

  public AllocateClass(Cloner cloner, AllocateClass original)
    : base(cloner, original) {
    Path = cloner.CloneType(original.Path);
    if (original.Bindings != null) {
      Bindings = new ActualBindings(cloner, original.Bindings);
    }

    if (cloner.CloneResolvedFields) {
      InitCall = cloner.CloneStmt(original.InitCall, false) as CallStmt;
    }
  }

  public List<Expression>? Arguments => Bindings?.Arguments;

  public AllocateClass Clone(Cloner cloner) {
    return new AllocateClass(cloner, this);
  }


  public override bool CanAffectPreviouslyKnownExpressions {
    get {
      if (InitCall != null) {
        foreach (var mod in InitCall.Method.Mod.Expressions!) {
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

  public override IEnumerable<INode> Children {
    get {
      if (Type == null) {
        return PreResolveChildren;
      }

      if (InitCall != null) {
        return new[] { InitCall };
      }

      return SubExpressions.Concat<Node>(SubStatements);
    }
  }
  public override IEnumerable<INode> PreResolveChildren =>
    new[] { Path }.OfType<Node>()
      .Concat((Bindings is { ArgumentBindings: not null } ?
                      Bindings.ArgumentBindings.Select(a => a.Actual) : null) ??
                    (Bindings != null ? Arguments : null) ??
                    Enumerable.Empty<Node>());
}