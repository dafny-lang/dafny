using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// An PrefixPredicate is the inductive unrolling P# implicitly declared for every extreme predicate P.
/// </summary>
public class PrefixPredicate : Function {
  public override string WhatKind => "prefix predicate";
  public override string WhatKindMentionGhost => WhatKind;
  public readonly Formal K;
  public readonly ExtremePredicate ExtremePred;
  public PrefixPredicate(RangeToken rangeToken, Name name, bool hasStaticKeyword,
    List<TypeParameter> typeArgs, Formal k, List<Formal> formals,
    List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
    Expression body, Attributes attributes, ExtremePredicate extremePred)
    : base(rangeToken, name, hasStaticKeyword, true, false, typeArgs, formals, null, Type.Bool, req, reads, ens, decreases, body, null, null, attributes, null) {
    Contract.Requires(k != null);
    Contract.Requires(extremePred != null);
    Contract.Requires(formals != null && 1 <= formals.Count && formals[0] == k);
    K = k;
    ExtremePred = extremePred;
  }
}