#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

[SyntaxBaseType(typeof(Declaration))]
public class Lemma : Method {
  public override string WhatKind => "lemma";
  public override string WhatKindMentionGhost => WhatKind;

  [SyntaxConstructor]
  public Lemma(IOrigin origin, Name nameNode,
    bool hasStaticKeyword,
    [Captured] List<TypeParameter> typeArgs,
    [Captured] List<Formal> ins, [Captured] List<Formal> outs,
    [Captured] List<AttributedExpression> req,
    [Captured] Specification<FrameExpression> reads,
    [Captured] Specification<FrameExpression> mod,
    [Captured] List<AttributedExpression> ens,
    [Captured] Specification<Expression> decreases,
    [Captured] BlockStmt body,
    Attributes? attributes, IOrigin? signatureEllipsis)
    : base(origin, nameNode, attributes, hasStaticKeyword, true,
      typeArgs, ins, req, ens, reads, decreases, outs, mod, body, signatureEllipsis) {
  }

  public Lemma(Cloner cloner, Lemma lemma) : base(cloner, lemma) {
  }

  public override bool AllowsAllocation => false;
}

public class TwoStateLemma : Method {
  public override string WhatKind => "twostate lemma";
  public override string WhatKindMentionGhost => WhatKind;

  public TwoStateLemma(IOrigin origin, Name nameNode,
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
    : base(origin, nameNode, attributes, hasStaticKeyword, true, typeArgs, ins, req, ens, reads, decreases, outs, mod, body, signatureEllipsis) {
    Contract.Requires(origin != null);
    Contract.Requires(nameNode != null);
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