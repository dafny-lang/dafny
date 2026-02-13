#nullable enable

using System.Collections.Generic;

namespace Microsoft.Dafny;

public class SeqType : CollectionType {
  [SyntaxConstructor]
  public SeqType(IOrigin? origin, List<Type?> typeArgs) : base(origin, typeArgs) { }

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