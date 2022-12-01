using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/**
   * Used by two phase constructors: https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#13323-two-phase-constructors
   */
public class DividedBlockStmt : BlockStmt {
  public readonly List<Statement> BodyInit;  // first part of Body's statements
  public readonly IToken SeparatorTok;  // token that separates the two parts, if any
  public readonly List<Statement> BodyProper;  // second part of Body's statements
  public DividedBlockStmt(IToken tok, IToken endTok, List<Statement> bodyInit, IToken/*?*/ separatorTok, List<Statement> bodyProper)
    : base(tok, endTok, Util.Concat(bodyInit, bodyProper)) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(cce.NonNullElements(bodyInit));
    Contract.Requires(cce.NonNullElements(bodyProper));
    this.BodyInit = bodyInit;
    this.SeparatorTok = separatorTok;
    this.BodyProper = bodyProper;
  }
  public override void AppendStmt(Statement s) {
    BodyProper.Add(s);
    base.AppendStmt(s);
  }
}