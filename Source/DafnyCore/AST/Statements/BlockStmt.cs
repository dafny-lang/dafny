using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class BlockStmt : Statement, IRegion {
  public readonly List<Statement> Body;

  IToken IRegion.BodyStartTok => Tok;
  IToken IRegion.BodyEndTok => EndTok;

  public BlockStmt(IToken tok, IToken endTok, [Captured] List<Statement> body)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(cce.NonNullElements(body));
    this.Body = body;
  }

  public override IEnumerable<Statement> SubStatements {
    get { return Body; }
  }

  public virtual void AppendStmt(Statement s) {
    Contract.Requires(s != null);
    Body.Add(s);
  }
}