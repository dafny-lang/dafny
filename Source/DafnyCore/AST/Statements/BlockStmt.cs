#nullable enable
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class BlockStmt : BlockLikeStmt {

  public override List<Statement> Body { get; }

  public BlockStmt(Cloner cloner, BlockLikeStmt original) : base(cloner, original)
  {
    Body = original.Body.Select(stmt => cloner.CloneStmt(stmt, false)).ToList();
  }

  [SyntaxConstructor]
  public BlockStmt(IOrigin origin, List<Statement> body, Attributes? attributes = null) : base(origin, attributes)
  {
    Body = body;
  }

  public override void AppendStmt(Statement s) {
    Body.Add(s);
  }

  public override void Prepend(Statement s) {
    Body.Insert(0, s);
  }
}