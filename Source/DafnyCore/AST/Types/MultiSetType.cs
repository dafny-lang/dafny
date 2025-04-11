#nullable enable

using System.Collections.Generic;

namespace Microsoft.Dafny;

public class MultiSetType : CollectionType {
  [SyntaxConstructor]
  public MultiSetType(IOrigin? origin, List<Type?> typeArgs) : base(origin, typeArgs) { }

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