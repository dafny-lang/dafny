using System.Collections.Generic;
using System.Diagnostics.Contracts;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public class Constructor : Method {
  public override string WhatKind => "constructor";
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Body == null || Body is DividedBlockStmt);
  }

  public override SymbolKind? Kind => SymbolKind.Constructor;
  protected override string GetQualifiedName() {
    return EnclosingClass.Name;
  }

  public List<Statement> BodyInit {  // first part of Body's statements
    get {
      if (Body == null) {
        return null;
      } else {
        return ((DividedBlockStmt)Body).BodyInit;
      }
    }
  }
  public List<Statement> BodyProper {  // second part of Body's statements
    get {
      if (Body == null) {
        return null;
      } else {
        return ((DividedBlockStmt)Body).BodyProper;
      }
    }
  }
  public Constructor(RangeToken rangeToken, Name name,
    bool isGhost,
    List<TypeParameter> typeArgs,
    List<Formal> ins,
    List<AttributedExpression> req,
    Specification<FrameExpression> reads,
    [Captured] Specification<FrameExpression> mod,
    List<AttributedExpression> ens,
    Specification<Expression> decreases,
    DividedBlockStmt body,
    Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, false, isGhost, typeArgs, ins, new List<Formal>(), req, reads, mod, ens, decreases, body, attributes, signatureEllipsis) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(Cce.NonNullElements(typeArgs));
    Contract.Requires(Cce.NonNullElements(ins));
    Contract.Requires(Cce.NonNullElements(req));
    Contract.Requires(mod != null);
    Contract.Requires(Cce.NonNullElements(ens));
    Contract.Requires(decreases != null);
  }

  public Constructor(Cloner cloner, Constructor original) : base(cloner, original) {
  }

  public bool HasName {
    get {
      return Name != "_ctor";
    }
  }
}