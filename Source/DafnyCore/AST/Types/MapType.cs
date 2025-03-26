#nullable enable

using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class MapType : CollectionType {
  public bool Finite { get; }

  public Type Domain => Arg!;

  /// <summary>
  /// Must not be called unless <see cref="range"/> is set.
  /// </summary>
  public Type Range {
    get {
      Contract.Assume(range != null);
      return range!;
    }
  }
  private Type? range;

  public override void SetTypeArgs(Type? domain, Type? range) {
    base.SetTypeArgs(domain, range);
    Contract.Assume(this.range == null);  // Can only set once.  This is really a precondition.
    this.range = range;
  }

  [SyntaxConstructor]
  public MapType(IOrigin? origin, bool finite, List<Type?> collectionTypeArgs) : base(origin, collectionTypeArgs) {
    Contract.Requires(collectionTypeArgs is [null, null] or [not null, not null]);
    Finite = finite;
    range = collectionTypeArgs[1];
  }

  public MapType(bool finite, Type? domain, Type? range) : base(domain, range) {
    Finite = finite;
  }

  public MapType(Cloner cloner, MapType original) : base(cloner, original) {
    Finite = original.Finite;
    range = cloner.CloneType(original.Range);
    var arg = HasTypeArg() ? Arg : null;
    TypeArgs = [arg, range];
  }

  public override string CollectionTypeName => Finite ? "map" : "imap";

  [System.Diagnostics.Contracts.Pure]
  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    var targs = HasTypeArg() ? this.TypeArgsToString(options, context, parseAble)! : "";
    return CollectionTypeName + targs;
  }
  public override bool Equals(Type that, bool keepConstraints = false) {
    var t = that.NormalizeExpand(keepConstraints) as MapType;
    return t != null && Finite == t.Finite && Arg!.Equals(t.Arg, keepConstraints) && Range.Equals(t.Range, keepConstraints);
  }

  public override Type Subst(IDictionary<TypeParameter, Type> subst) {
    var dom = Domain.Subst(subst);
    if (dom is InferredTypeProxy) {
      ((InferredTypeProxy)dom).KeepConstraints = true;
    }
    var ran = Range.Subst(subst);
    if (ran is InferredTypeProxy) {
      ((InferredTypeProxy)ran).KeepConstraints = true;
    }
    if (dom == Domain && ran == Range) {
      return this;
    } else {
      return new MapType(Finite, dom, ran);
    }
  }

  public override Type ReplaceTypeArguments(List<Type> arguments) {
    return new MapType(Finite, arguments[0], arguments[1]);
  }

  // A map type supports equality if both its Keys type and Values type does.  It is checked
  // that the Keys type always supports equality, so we only need to check the Values type here.
  public override bool SupportsEquality => range!.SupportsEquality;

  public override bool ComputeMayInvolveReferences(ISet<DatatypeDecl> visitedDatatypes) {
    return Domain.ComputeMayInvolveReferences(visitedDatatypes) || Range.ComputeMayInvolveReferences(visitedDatatypes);
  }

  public override BinaryExpr.ResolvedOpcode ResolvedOpcodeForIn => BinaryExpr.ResolvedOpcode.InMap;
  public override CollectionBoundedPool GetBoundedPool(Expression source) {
    return new MapBoundedPool(source, Domain, Domain, Finite);
  }
}