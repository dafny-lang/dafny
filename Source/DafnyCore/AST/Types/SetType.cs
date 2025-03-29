#nullable enable

using System.Collections.Generic;

namespace Microsoft.Dafny;

public class SetType : CollectionType {
  public bool Finite { get; }

  [SyntaxConstructor]
  public SetType(IOrigin? origin, bool finite, List<Type?> typeArgs) : base(origin, typeArgs) {
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