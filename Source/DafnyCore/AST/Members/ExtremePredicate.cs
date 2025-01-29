using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class ExtremePredicate : Function {
  public override string WhatKindMentionGhost => WhatKind;
  public enum KType { Unspecified, Nat, ORDINAL }
  public readonly KType TypeOfK;
  public bool KNat {
    get {
      return TypeOfK == KType.Nat;
    }
  }
  [FilledInDuringResolution] public readonly List<FunctionCallExpr> Uses = [];  // used by verifier
  [FilledInDuringResolution] public PrefixPredicate PrefixPredicate;  // (name registration)

  public override IEnumerable<INode> Children => base.Children.Concat(new[] { PrefixPredicate });
  public override IEnumerable<INode> PreResolveChildren => base.Children;

  public ExtremePredicate(IOrigin rangeOrigin, Name name, bool hasStaticKeyword, bool isOpaque, KType typeOfK,
    List<TypeParameter> typeArgs, List<Formal> ins, Formal result,
    List<AttributedExpression> req, Specification<FrameExpression> reads, List<AttributedExpression> ens,
    Expression body, Attributes attributes, IOrigin signatureEllipsis)
    : base(rangeOrigin, name, hasStaticKeyword, true, isOpaque, typeArgs, ins, result, Type.Bool,
      req, reads, ens, new Specification<Expression>([], null), body, null, null, attributes, signatureEllipsis) {
    TypeOfK = typeOfK;
  }

  /// <summary>
  /// For the given call P(s), return P#[depth](s).  The resulting expression shares some of the subexpressions
  /// with 'fexp' (that is, what is returned is not necessarily a clone).
  /// </summary>
  public FunctionCallExpr CreatePrefixPredicateCall(FunctionCallExpr fexp, Expression depth) {
    Contract.Requires(fexp != null);
    Contract.Requires(fexp.Function == this);
    Contract.Requires(depth != null);
    Contract.Ensures(Contract.Result<FunctionCallExpr>() != null);

    var args = new List<Expression>() { depth };
    args.AddRange(fexp.Args);
    var prefixPredCall = new FunctionCallExpr(fexp.Origin, PrefixPredicate.NameNode, fexp.Receiver, fexp.OpenParen, fexp.CloseParen, args);
    prefixPredCall.Function = this.PrefixPredicate;  // resolve here
    prefixPredCall.TypeApplication_AtEnclosingClass = fexp.TypeApplication_AtEnclosingClass;  // resolve here
    prefixPredCall.TypeApplication_JustFunction = fexp.TypeApplication_JustFunction;  // resolve here
    prefixPredCall.Type = fexp.Type;  // resolve here
    prefixPredCall.CoCall = fexp.CoCall;  // resolve here
    return prefixPredCall;
  }
}

public class GreatestPredicate : ExtremePredicate {
  public override string WhatKind => "greatest predicate";
  public GreatestPredicate(IOrigin rangeOrigin, Name name, bool hasStaticKeyword, bool isOpaque, KType typeOfK,
    List<TypeParameter> typeArgs, List<Formal> ins, Formal result,
    List<AttributedExpression> req, Specification<FrameExpression> reads, List<AttributedExpression> ens,
    Expression body, Attributes attributes, IOrigin signatureEllipsis)
    : base(rangeOrigin, name, hasStaticKeyword, isOpaque, typeOfK, typeArgs, ins, result,
      req, reads, ens, body, attributes, signatureEllipsis) {
  }
}

public class LeastPredicate : ExtremePredicate {
  public override string WhatKind => "least predicate";
  public LeastPredicate(IOrigin rangeOrigin, Name name, bool hasStaticKeyword, bool isOpaque, KType typeOfK,
    List<TypeParameter> typeArgs, List<Formal> ins, Formal result,
    List<AttributedExpression> req, Specification<FrameExpression> reads, List<AttributedExpression> ens,
    Expression body, Attributes attributes, IOrigin signatureEllipsis)
    : base(rangeOrigin, name, hasStaticKeyword, isOpaque, typeOfK, typeArgs, ins, result,
      req, reads, ens, body, attributes, signatureEllipsis) {
  }
}