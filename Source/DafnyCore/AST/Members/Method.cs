#nullable enable
using System.Collections.Generic;
using DafnyCore;

namespace Microsoft.Dafny;

public class Method : MethodOrConstructor {
  public override List<Formal> Outs { get; }

  public override bool HasStaticKeyword { get; }

  public Method(Cloner cloner, Method original) : base(cloner, original)
  {
    Outs = original.Outs.ConvertAll(p => cloner.CloneFormal(p, false));
    HasStaticKeyword = original.HasStaticKeyword;
  }

  public Method(IOrigin origin, Name nameNode, Attributes? attributes, bool hasStaticKeyword, 
    bool isGhost, List<TypeParameter> typeArgs, List<Formal> ins, List<AttributedExpression> req, 
    List<AttributedExpression> ens, Specification<FrameExpression> reads, Specification<Expression> decreases, 
    List<Formal> outs, Specification<FrameExpression> mod, BlockStmt body, IOrigin? signatureEllipsis, bool isByMethod = false) 
    : base(origin, nameNode, attributes, isGhost, typeArgs, ins, req, ens, reads, decreases, mod, body, signatureEllipsis, isByMethod)
  {
    Outs = outs;
    HasStaticKeyword = hasStaticKeyword;
  }
}