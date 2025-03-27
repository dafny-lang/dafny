using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// A PrefixLemma is the inductive unrolling M# implicitly declared for every extreme lemma M.
/// </summary>
public class PrefixLemma : Method {
  public override string WhatKind => "prefix lemma";
  public override string WhatKindMentionGhost => WhatKind;

  public Formal K;
  public ExtremeLemma ExtremeLemma;
  public PrefixLemma(IOrigin origin, Name nameNode, bool hasStaticKeyword,
    List<TypeParameter> typeArgs, Formal k, List<Formal> ins, List<Formal> outs,
    List<AttributedExpression> req, [Captured] Specification<FrameExpression> reads,
    Specification<FrameExpression> mod, List<AttributedExpression> ens, Specification<Expression> decreases,
    BlockStmt body, Attributes attributes, ExtremeLemma extremeLemma)
    : base(origin, nameNode, attributes, hasStaticKeyword, true, typeArgs, ins, req, ens, reads, decreases, outs, mod, body, null) {
    Contract.Requires(k != null);
    Contract.Requires(ins != null && 1 <= ins.Count && ins[0] == k);
    Contract.Requires(extremeLemma != null);
    K = k;
    ExtremeLemma = extremeLemma;
  }

  public override bool AllowsAllocation => false;
}