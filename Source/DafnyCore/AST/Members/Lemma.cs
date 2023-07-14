using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class Lemma : Method {
  public override string WhatKind => "lemma";
  public override string WhatKindMentionGhost => WhatKind;
  public Lemma(RangeToken rangeToken, Name name,
    bool hasStaticKeyword,
    [Captured] List<TypeParameter> typeArgs,
    [Captured] List<Formal> ins, [Captured] List<Formal> outs,
    [Captured] List<AttributedExpression> req, [Captured] Specification<FrameExpression> mod,
    [Captured] List<AttributedExpression> ens,
    [Captured] Specification<Expression> decreases,
    [Captured] BlockStmt body,
    Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, hasStaticKeyword, true, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes, signatureEllipsis) {
  }

  public Lemma(Cloner cloner, Lemma lemma) : base(cloner, lemma) {
  }

  public override bool AllowsAllocation => false;
}

public class TwoStateLemma : Method {
  public override string WhatKind => "twostate lemma";
  public override string WhatKindMentionGhost => WhatKind;

  public TwoStateLemma(RangeToken rangeToken, Name name,
    bool hasStaticKeyword,
    [Captured] List<TypeParameter> typeArgs,
    [Captured] List<Formal> ins, [Captured] List<Formal> outs,
    [Captured] List<AttributedExpression> req,
    [Captured] Specification<FrameExpression> mod,
    [Captured] List<AttributedExpression> ens,
    [Captured] Specification<Expression> decreases,
    [Captured] BlockStmt body,
    Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, hasStaticKeyword, true, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes, signatureEllipsis) {
    Contract.Requires(rangeToken != null);
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