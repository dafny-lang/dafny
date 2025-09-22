#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public class Constructor : MethodOrConstructor {
  private DividedBlockStmt? body;
  public override List<Formal> Outs => [];

  public override string WhatKind => "constructor";
  public override bool HasStaticKeyword => false;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Body == null || Body is DividedBlockStmt);
  }

  public override SymbolKind? Kind => SymbolKind.Constructor;
  protected override string GetQualifiedName() {
    return EnclosingClass.Name;
  }

  public List<Statement>? BodyInit => Body?.BodyInit;

  public List<Statement>? BodyProper => Body?.BodyProper;

  [SyntaxConstructor]
  public Constructor(IOrigin origin, Name nameNode,
    bool isGhost,
    List<TypeParameter> typeArgs,
    List<Formal> ins,
    List<AttributedExpression> req,
    Specification<FrameExpression> reads,
    [Captured] Specification<FrameExpression> mod,
    List<AttributedExpression> ens,
    Specification<Expression> decreases,
    DividedBlockStmt? body,
    Attributes? attributes, IOrigin? signatureEllipsis
    )
    : base(origin, nameNode, attributes, isGhost, typeArgs, ins, req, ens, reads, decreases, mod,
       signatureEllipsis) {
    this.body = body;
    Contract.Requires(origin != null);
    Contract.Requires(nameNode != null);
    Contract.Requires(Cce.NonNullElements(typeArgs));
    Contract.Requires(Cce.NonNullElements(ins));
    Contract.Requires(Cce.NonNullElements(req));
    Contract.Requires(mod != null);
    Contract.Requires(Cce.NonNullElements(ens));
    Contract.Requires(decreases != null);
  }

  public Constructor(Cloner cloner, Constructor original) : base(cloner, original) {
    body = cloner.CloneDividedBlockStmt(original.Body);
  }

  public bool HasName {
    get {
      return Name != "_ctor";
    }
  }

  public override DividedBlockStmt? Body => body;
  public override void SetBody(BlockLikeStmt newBody) {
    body = newBody is BlockStmt blockStmt
      ? new DividedBlockStmt(blockStmt.Origin, blockStmt.Body, null, [], []) : (DividedBlockStmt)newBody;
  }
}