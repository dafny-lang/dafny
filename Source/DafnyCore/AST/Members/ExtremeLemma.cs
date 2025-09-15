#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

[SyntaxBaseType(typeof(Declaration))]
public abstract class ExtremeLemma : Method {
  public override string WhatKindMentionGhost => WhatKind;
  public ExtremePredicate.KType TypeOfK;
  public bool KNat => TypeOfK == ExtremePredicate.KType.Nat;
  [FilledInDuringResolution] public PrefixLemma PrefixLemma = null!;  // (name registration)

  public override IEnumerable<INode> Children => base.Children.Concat(PrefixLemma == null ? [] : [PrefixLemma]);

  public override IEnumerable<INode> PreResolveChildren => base.Children;

  public ExtremeLemma(Cloner cloner, ExtremeLemma lemma) : base(cloner, lemma) {
    TypeOfK = lemma.TypeOfK;
  }

  [SyntaxConstructor]
  protected ExtremeLemma(IOrigin origin, Name nameNode,
    bool hasStaticKeyword, ExtremePredicate.KType typeOfK,
    List<TypeParameter> typeArgs,
    List<Formal> ins, [Captured] List<Formal> outs,
    List<AttributedExpression> req,
    Specification<FrameExpression> reads,
    [Captured] Specification<FrameExpression> mod,
    List<AttributedExpression> ens,
    Specification<Expression> decreases,
    BlockStmt body,
    Attributes? attributes, IOrigin? signatureEllipsis)
    : base(origin, nameNode, attributes, hasStaticKeyword, true,
      typeArgs, ins, req, ens, reads, decreases, outs, mod, body, signatureEllipsis) {
    Contract.Requires(origin != null);
    Contract.Requires(nameNode != null);
    Contract.Requires(Cce.NonNullElements(typeArgs));
    Contract.Requires(Cce.NonNullElements(ins));
    Contract.Requires(Cce.NonNullElements(outs));
    Contract.Requires(Cce.NonNullElements(req));
    Contract.Requires(mod != null);
    Contract.Requires(Cce.NonNullElements(ens));
    Contract.Requires(decreases != null);
    TypeOfK = typeOfK;
  }

  public override bool AllowsAllocation => false;
}