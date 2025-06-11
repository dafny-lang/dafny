#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

[SyntaxBaseType(typeof(MethodOrFunction))]
public class Predicate : Function {
  public override string WhatKind => "predicate";
  public enum BodyOriginKind {
    OriginalOrInherited,  // this predicate definition is new (and the predicate may or may not have a body), or the predicate's body (whether or not it exists) is being inherited unmodified (from the previous refinement--it may be that the inherited body was itself an extension, for example)
    DelayedDefinition,  // this predicate declaration provides, for the first time, a body--the declaration refines a previously declared predicate, but the previous one had no body
    Extension  // this predicate extends the definition of a predicate with a body in a module being refined
  }
  public BodyOriginKind BodyOrigin;

  [SyntaxConstructor]
  public Predicate(IOrigin origin, Name nameNode, bool hasStaticKeyword, bool isGhost, bool isOpaque,
    List<TypeParameter> typeArgs, List<Formal> ins,
    Formal? result,
    List<AttributedExpression> req,
    Specification<FrameExpression> reads,
    List<AttributedExpression> ens, Specification<Expression> decreases,
    Expression? body, BodyOriginKind bodyOrigin, IOrigin? byMethodTok,
    BlockStmt? byMethodBody, Attributes? attributes, IOrigin? signatureEllipsis)
    : base(origin, nameNode, hasStaticKeyword, isGhost, isOpaque, typeArgs, ins,
      result, Type.Bool, req, reads, ens, decreases, body,
      byMethodTok, byMethodBody, attributes, signatureEllipsis) {
    Contract.Requires(bodyOrigin == Predicate.BodyOriginKind.OriginalOrInherited || body != null);
    BodyOrigin = bodyOrigin;
  }
}