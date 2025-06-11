#nullable enable
using System.Collections.Generic;

namespace Microsoft.Dafny;

public class GreatestPredicate : ExtremePredicate {
  public override string WhatKind => "greatest predicate";

  [SyntaxConstructor]
  public GreatestPredicate(IOrigin origin, Name nameNode, bool hasStaticKeyword, bool isOpaque, KType typeOfK,
    List<TypeParameter> typeArgs, List<Formal> ins, Formal? result,
    List<AttributedExpression> req, Specification<FrameExpression> reads, List<AttributedExpression> ens,
    Expression body, Attributes? attributes, IOrigin? signatureEllipsis)
    : base(origin, nameNode, hasStaticKeyword, isOpaque, typeOfK, typeArgs, ins, result,
      req, reads, ens, body, attributes, signatureEllipsis) {
  }
}