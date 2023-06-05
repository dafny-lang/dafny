using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class Predicate : Function {
  public override string WhatKind => "predicate";
  public enum BodyOriginKind {
    OriginalOrInherited,  // this predicate definition is new (and the predicate may or may not have a body), or the predicate's body (whether or not it exists) is being inherited unmodified (from the previous refinement--it may be that the inherited body was itself an extension, for example)
    DelayedDefinition,  // this predicate declaration provides, for the first time, a body--the declaration refines a previously declared predicate, but the previous one had no body
    Extension  // this predicate extends the definition of a predicate with a body in a module being refined
  }
  public readonly BodyOriginKind BodyOrigin;
  public Predicate(RangeToken rangeToken, Name name, bool hasStaticKeyword, bool isGhost, bool isOpaque,
    List<TypeParameter> typeArgs, List<Formal> formals,
    Formal result,
    List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
    Expression body, BodyOriginKind bodyOrigin, IToken/*?*/ byMethodTok, BlockStmt/*?*/ byMethodBody, Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, hasStaticKeyword, isGhost, isOpaque, typeArgs, formals, result, Type.Bool, req, reads, ens, decreases, body, byMethodTok, byMethodBody, attributes, signatureEllipsis) {
    Contract.Requires(bodyOrigin == Predicate.BodyOriginKind.OriginalOrInherited || body != null);
    BodyOrigin = bodyOrigin;
  }
}