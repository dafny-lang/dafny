using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class BlockStmt : Statement, ICloneable<BlockStmt>, ICanFormat {
  public readonly List<Statement> Body;

  public BlockStmt Clone(Cloner cloner) {
    return new BlockStmt(cloner, this);
  }

  public BlockStmt(Cloner cloner, BlockStmt original) : base(cloner, original) {
    Body = original.Body.Select(cloner.CloneStmt).ToList();
  }

  public BlockStmt(RangeToken rangeToken, [Captured] List<Statement> body)
    : base(rangeToken) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(cce.NonNullElements(body));
    this.Body = body;
  }

  public override IEnumerable<Statement> SubStatements => Body;

  public virtual void AppendStmt(Statement s) {
    Contract.Requires(s != null);
    Body.Add(s);
  }

  public bool SetIndent(int indentBefore, IndentationFormatter formatter) {
    var braceIndent = indentBefore;
    var innerBlockIndent = indentBefore + formatter.SpaceTab;
    foreach (var token in OwnedTokens) {
      if (formatter.SetIndentLabelTokens(token, indentBefore)) {
        continue;
      }
      switch (token.val) {
        case "{": {
            if (!formatter.TryGetIndentLineBefore(token, out var indentLineBefore)) {
              formatter.SetDelimiterIndentedRegions(token, braceIndent);
            } else {
              braceIndent = indentLineBefore;
              if (!formatter.TryGetIndentBefore(token, out _)) {
                formatter.SetDelimiterIndentedRegions(token, braceIndent);
              }

              if (!IndentationFormatter.IsFollowedByNewline(token)) {
                // Align statements
                formatter.SetAlign(indentBefore, token, out innerBlockIndent, out braceIndent);
              }
            }

            break;
          }
        case "}": {
            formatter.SetIndentations(token, braceIndent + formatter.SpaceTab, braceIndent, indentBefore);
            break;
          }
      }
    }

    foreach (var blockStmtBody in Body) {
      if (blockStmtBody is not BlockStmt && OwnedTokens.Any()) {
        formatter.SetIndentations(blockStmtBody.StartToken, innerBlockIndent, innerBlockIndent);
      }

      formatter.Visit(blockStmtBody, indentBefore + formatter.SpaceTab);
    }

    return false;
  }
}