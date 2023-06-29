using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class TwoStateFunction : Function {
  public override string WhatKind => "twostate function";
  public override string WhatKindMentionGhost => WhatKind;
  public TwoStateFunction(RangeToken rangeToken, Name name, bool hasStaticKeyword, bool isOpaque,
    List<TypeParameter> typeArgs, List<Formal> formals, Formal result, Type resultType,
    List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
    Expression body, Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, hasStaticKeyword, true, isOpaque, typeArgs, formals, result, resultType, req, reads, ens, decreases, body, null, null, attributes, signatureEllipsis) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(typeArgs != null);
    Contract.Requires(formals != null);
    Contract.Requires(resultType != null);
    Contract.Requires(req != null);
    Contract.Requires(reads != null);
    Contract.Requires(ens != null);
    Contract.Requires(decreases != null);
  }
  public override bool ReadsHeap { get { return true; } }
}

public class TwoStatePredicate : TwoStateFunction {
  public override string WhatKind => "twostate predicate";
  public TwoStatePredicate(RangeToken rangeToken, Name name, bool hasStaticKeyword, bool isOpaque,
    List<TypeParameter> typeArgs, List<Formal> formals, Formal result,
    List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
    Expression body, Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, hasStaticKeyword, isOpaque, typeArgs, formals, result, Type.Bool, req, reads, ens, decreases, body, attributes, signatureEllipsis) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(typeArgs != null);
    Contract.Requires(formals != null);
    Contract.Requires(req != null);
    Contract.Requires(reads != null);
    Contract.Requires(ens != null);
    Contract.Requires(decreases != null);
  }
}