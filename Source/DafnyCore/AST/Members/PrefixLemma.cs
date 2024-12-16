using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// A PrefixLemma is the inductive unrolling M# implicitly declared for every extreme lemma M.
/// </summary>
public class PrefixLemma : Method {
  public override string WhatKind => "prefix lemma";
  public override string WhatKindMentionGhost => WhatKind;

  public readonly Formal K;
  public readonly ExtremeLemma ExtremeLemma;
  public PrefixLemma(IOrigin rangeOrigin, Name name, bool hasStaticKeyword,
    List<TypeParameter> typeArgs, Formal k, List<Formal> ins, List<Formal> outs,
    List<AttributedExpression> req, [Captured] Specification<FrameExpression> reads,
    Specification<FrameExpression> mod, List<AttributedExpression> ens, Specification<Expression> decreases,
    BlockStmt body, Attributes attributes, ExtremeLemma extremeLemma)
    : base(rangeOrigin, name, hasStaticKeyword, true, typeArgs, ins, outs, req, reads, mod, ens, decreases, body, attributes, null) {
    Contract.Requires(k != null);
    Contract.Requires(ins != null && 1 <= ins.Count && ins[0] == k);
    Contract.Requires(extremeLemma != null);
    K = k;
    ExtremeLemma = extremeLemma;
  }

  public override bool AllowsAllocation => false;
}