#nullable enable

using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class CollectionType : NonProxyType {
  public abstract string CollectionTypeName { get; }
  public override IEnumerable<Node> Nodes => TypeArgs.SelectMany(ta => ta.Nodes);

  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    var targs = HasTypeArg() ? this.TypeArgsToString(options, context, parseAble) : "";
    return CollectionTypeName + targs;
  }

  // Only used for SyntaxConstructor
  public List<Type> CollectionTypeArgs => TypeArgs;

  [FilledInDuringResolution]
  public Type? Arg { get; private set; }  // denotes the Domain type for a Map

  public Type? ValueArg => TypeArgs.Last();

  // The following methods, HasTypeArg and SetTypeArg/SetTypeArgs, are to be called during resolution to make sure that "arg" becomes set.
  public bool HasTypeArg() {
    return Arg != null;
  }

  public void SetTypeArg(Type? arg) {
    Contract.Assume(Arg == null);  // Can only set it once.  This is really a precondition.
    Arg = arg;

    Debug.Assert(TypeArgs.Count == 0);
    TypeArgs.Add(arg);
  }

  public virtual void SetTypeArgs(Type? arg, Type? other) {
    Contract.Assume(Arg == null);  // Can only set it once.  This is really a precondition.
    Arg = arg;

    Debug.Assert(TypeArgs.Count == 0);
    TypeArgs.Add(arg);
    TypeArgs.Add(other);
  }

  [ContractInvariantMethod]
  void ObjectInvariant() {
    // Contract.Invariant(Contract.ForAll(TypeArgs, tp => tp != null));
    // After resolution, the following is invariant:  Contract.Invariant(Arg != null);
    // However, it may not be true until then.
  }

  /// <summary>
  /// Construct a collection type with either 1 or 2 type arguments.
  /// </summary>
  [SyntaxConstructor]
  protected CollectionType(IOrigin? origin, List<Type?> collectionTypeArgs) : base(origin) {
    Contract.Requires(collectionTypeArgs is [_] or [null, null] or [not null, not null]);
    Arg = collectionTypeArgs.FirstOrDefault();
    if (collectionTypeArgs is [not null] or [not null, not null]) {
      TypeArgs = collectionTypeArgs;
    }
  }

  /// <summary>
  /// This constructor is a collection types with 1 type argument
  /// </summary>
  protected CollectionType(Type? arg) {
    Arg = arg;
    TypeArgs = new List<Type>(1);
    if (arg != null) {
      TypeArgs.Add(arg);
    }
  }

  /// <summary>
  /// This constructor is a collection types with 2 type arguments
  /// </summary>
  protected CollectionType(Type? arg, Type? other) {
    Arg = arg;
    TypeArgs = new List<Type>(2);
    if (arg != null && other != null) {
      TypeArgs.Add(arg);
      TypeArgs.Add(other);
    }
    Debug.Assert(arg == null && other == null || arg != null && other != null);
  }

  protected CollectionType(Cloner cloner, CollectionType original) {
    Arg = cloner.CloneType(original.Arg);
  }

  public override bool ComputeMayInvolveReferences(ISet<DatatypeDecl> visitedDatatypes) {
    return Arg!.ComputeMayInvolveReferences(visitedDatatypes);
  }

  /// <summary>
  /// This property returns the ResolvedOpcode for the "in" operator when used with this collection type.
  /// </summary>
  public abstract BinaryExpr.ResolvedOpcode ResolvedOpcodeForIn { get; }

  /// <summary>
  /// For a given "source", denoting an expression of this CollectionType, return the BoundedPool corresponding
  /// to an expression "x in source".
  /// </summary>
  public abstract CollectionBoundedPool GetBoundedPool(Expression source);
}

public class SetType : CollectionType {
  public bool Finite { get; }

  [SyntaxConstructor]
  public SetType(IOrigin? origin, bool finite, List<Type?> collectionTypeArgs) : base(origin, collectionTypeArgs) {
    Finite = finite;
  }

  public SetType(bool finite, Type? arg) : base(arg) {
    Finite = finite;
  }

  public override string CollectionTypeName => Finite ? "set" : "iset";

  [System.Diagnostics.Contracts.Pure]
  public override bool Equals(Type that, bool keepConstraints = false) {
    var t = that.NormalizeExpand(keepConstraints) as SetType;
    return t != null && Finite == t.Finite && Arg!.Equals(t.Arg, keepConstraints);
  }

  public override Type Subst(IDictionary<TypeParameter, Type> subst) {
    var arg = Arg?.Subst(subst);
    if (arg is InferredTypeProxy) {
      ((InferredTypeProxy)arg).KeepConstraints = true;
    }
    return arg == Arg ? this : new SetType(Finite, arg);
  }

  public override Type ReplaceTypeArguments(List<Type> arguments) {
    return new SetType(Finite, arguments[0]);
  }

  // Sets always support equality, because there is a check that the set element type always does.
  public override bool SupportsEquality => true;

  public override BinaryExpr.ResolvedOpcode ResolvedOpcodeForIn => BinaryExpr.ResolvedOpcode.InSet;
  public override CollectionBoundedPool GetBoundedPool(Expression source) {
    return new SetBoundedPool(source, Arg, Arg, Finite);
  }
}

public class MultiSetType : CollectionType {
  [SyntaxConstructor]
  public MultiSetType(IOrigin? origin, List<Type?> collectionTypeArgs) : base(origin, collectionTypeArgs) { }

  public MultiSetType(Type? arg) : base(arg) { }

  public override string CollectionTypeName => "multiset";

  public override bool Equals(Type that, bool keepConstraints = false) {
    var t = that.NormalizeExpand(keepConstraints) as MultiSetType;
    return t != null && Arg!.Equals(t.Arg, keepConstraints);
  }

  public override Type Subst(IDictionary<TypeParameter, Type> subst) {
    var arg = Arg?.Subst(subst);
    if (arg is InferredTypeProxy) {
      ((InferredTypeProxy)arg).KeepConstraints = true;
    }
    return arg == Arg ? this : new MultiSetType(arg);
  }

  public override Type ReplaceTypeArguments(List<Type> arguments) {
    return new MultiSetType(arguments[0]);
  }

  // Multisets always support equality, because there is a check that the set element type always does.
  public override bool SupportsEquality => true;

  public override BinaryExpr.ResolvedOpcode ResolvedOpcodeForIn => BinaryExpr.ResolvedOpcode.InMultiSet;
  public override CollectionBoundedPool GetBoundedPool(Expression source) {
    return new MultiSetBoundedPool(source, Arg, Arg);
  }
}

public class SeqType : CollectionType {
  [SyntaxConstructor]
  public SeqType(IOrigin? origin, List<Type?> collectionTypeArgs) : base(origin, collectionTypeArgs) { }

  public SeqType(Type? arg) : base(arg) { }

  public override string CollectionTypeName => "seq";

  public override bool Equals(Type that, bool keepConstraints = false) {
    var t = that.NormalizeExpand(keepConstraints) as SeqType;
    return t != null && Arg!.Equals(t.Arg, keepConstraints);
  }

  public override Type Subst(IDictionary<TypeParameter, Type> subst) {
    var arg = Arg?.Subst(subst);
    if (arg is InferredTypeProxy) {
      ((InferredTypeProxy)arg).KeepConstraints = true;
    }
    return arg == Arg ? this : new SeqType(arg);
  }

  public override Type ReplaceTypeArguments(List<Type> arguments) {
    return new SeqType(arguments[0]);
  }

  // The sequence type supports equality if its element type does
  public override bool SupportsEquality => Arg!.SupportsEquality;

  public override BinaryExpr.ResolvedOpcode ResolvedOpcodeForIn => BinaryExpr.ResolvedOpcode.InSeq;
  public override CollectionBoundedPool GetBoundedPool(Expression source) {
    return new SeqBoundedPool(source, Arg, Arg);
  }
}
