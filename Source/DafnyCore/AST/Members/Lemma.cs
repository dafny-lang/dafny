using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class Lemma : Method {
  public override string WhatKind => "lemma";
  public override string WhatKindMentionGhost => WhatKind;
  public Lemma(IOrigin rangeOrigin, Name name,
    bool hasStaticKeyword,
    [Captured] List<TypeParameter> typeArgs,
    [Captured] List<Formal> ins, [Captured] List<Formal> outs,
    [Captured] List<AttributedExpression> req,
    [Captured] Specification<FrameExpression> reads,
    [Captured] Specification<FrameExpression> mod,
    [Captured] List<AttributedExpression> ens,
    [Captured] Specification<Expression> decreases,
    [Captured] BlockStmt body,
    Attributes attributes, IOrigin signatureEllipsis)
    : base(rangeOrigin, name, hasStaticKeyword, true, typeArgs, ins, outs, req, reads, mod, ens, decreases, body, attributes, signatureEllipsis) {
  }

  public Lemma(Cloner cloner, Lemma lemma) : base(cloner, lemma) {
  }

  public override bool AllowsAllocation => false;
}

public class TwoStateLemma : Method {
  public override string WhatKind => "twostate lemma";
  public override string WhatKindMentionGhost => WhatKind;

  public TwoStateLemma(IOrigin rangeOrigin, Name name,
    bool hasStaticKeyword,
    [Captured] List<TypeParameter> typeArgs,
    [Captured] List<Formal> ins, [Captured] List<Formal> outs,
    [Captured] List<AttributedExpression> req,
    [Captured] Specification<FrameExpression> reads,
    [Captured] Specification<FrameExpression> mod,
    [Captured] List<AttributedExpression> ens,
    [Captured] Specification<Expression> decreases,
    [Captured] BlockStmt body,
    Attributes attributes, IOrigin signatureEllipsis)
    : base(rangeOrigin, name, hasStaticKeyword, true, typeArgs, ins, outs, req, reads, mod, ens, decreases, body, attributes, signatureEllipsis) {
    Contract.Requires(rangeOrigin != null);
    Contract.Requires(name != null);
    Contract.Requires(typeArgs != null);
    Contract.Requires(ins != null);
    Contract.Requires(outs != null);
    Contract.Requires(req != null);
    Contract.Requires(mod != null);
    Contract.Requires(ens != null);
    Contract.Requires(decreases != null);
  }

  public TwoStateLemma(Cloner cloner, TwoStateLemma lemma) : base(cloner, lemma) {
  }

  public override bool AllowsAllocation => false;
}