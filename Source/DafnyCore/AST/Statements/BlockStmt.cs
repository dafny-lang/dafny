using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class BlockStmt : Statement, ICloneable<BlockStmt> {
  public readonly List<Statement> Body;

  public BlockStmt Clone(Cloner cloner) {
    return new BlockStmt(cloner, this);
  }

  public BlockStmt(Cloner cloner, BlockStmt original) : base(cloner, original) {
    Body = original.Body.Select(cloner.CloneStmt).ToList();
  }

  public BlockStmt(IToken tok, RangeToken rangeToken, [Captured] List<Statement> body)
    : base(tok, rangeToken) {
    Contract.Requires(tok != null);
    Contract.Requires(rangeToken != null);
    Contract.Requires(cce.NonNullElements(body));
    this.Body = body;
  }

  public override IEnumerable<Statement> SubStatements => Body;

  public virtual void AppendStmt(Statement s) {
    Contract.Requires(s != null);
    Body.Add(s);
  }
}