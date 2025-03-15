using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// An PrefixPredicate is the inductive unrolling P# implicitly declared for every extreme predicate P.
/// </summary>
public class PrefixPredicate : Function {
  public override string WhatKind => "prefix predicate";
  public override string WhatKindMentionGhost => WhatKind;
  public Formal K;
  public ExtremePredicate ExtremePred;
  public PrefixPredicate(IOrigin rangeOrigin, Name nameNode, bool hasStaticKeyword,
    List<TypeParameter> typeArgs, Formal k, List<Formal> ins,
    List<AttributedExpression> req, Specification<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
    Expression body, Attributes attributes, ExtremePredicate extremePred)
    : base(rangeOrigin, nameNode, hasStaticKeyword, true, false, typeArgs, ins, null, Type.Bool, req, reads, ens, decreases, body, null, null, attributes, null) {
    Contract.Requires(k != null);
    Contract.Requires(extremePred != null);
    Contract.Requires(ins != null && 1 <= ins.Count && ins[0] == k);
    K = k;
    ExtremePred = extremePred;
  }
}