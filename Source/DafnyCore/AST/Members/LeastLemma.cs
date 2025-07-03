#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class LeastLemma : ExtremeLemma {
  public override string WhatKind => "least lemma";

  public LeastLemma(IOrigin origin, Name nameNode,
    bool hasStaticKeyword, ExtremePredicate.KType typeOfK,
    List<TypeParameter> typeArgs,
    List<Formal> ins, [Captured] List<Formal> outs,
    List<AttributedExpression> req,
    Specification<FrameExpression> reads,
    [Captured] Specification<FrameExpression> mod,
    List<AttributedExpression> ens,
    Specification<Expression> decreases,
    BlockStmt body,
    Attributes attributes, IOrigin signatureEllipsis)
    : base(origin, nameNode, hasStaticKeyword, typeOfK, typeArgs, ins, outs, req, reads, mod, ens, decreases, body, attributes, signatureEllipsis) {
    Contract.Requires(origin != null);
    Contract.Requires(nameNode != null);
    Contract.Requires(Cce.NonNullElements(typeArgs));
    Contract.Requires(Cce.NonNullElements(ins));
    Contract.Requires(Cce.NonNullElements(outs));
    Contract.Requires(Cce.NonNullElements(req));
    Contract.Requires(mod != null);
    Contract.Requires(Cce.NonNullElements(ens));
    Contract.Requires(decreases != null);
  }

  public LeastLemma(Cloner cloner, LeastLemma leastLemma) : base(cloner, leastLemma) {
  }
}