using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class BlockStmt : Statement, ICloneable<BlockStmt>, ICanFormat {
  public readonly List<Statement> Body;

  public BlockStmt Clone(Cloner cloner) {
    return new BlockStmt(cloner, this);
  }

  protected BlockStmt(Cloner cloner, BlockStmt original) : base(cloner, original) {
    Body = original.Body.Select(stmt => cloner.CloneStmt(stmt, false)).ToList();
  }

  public BlockStmt(IOrigin rangeOrigin, [Captured] List<Statement> body)
    : base(rangeOrigin) {
    Contract.Requires(rangeOrigin != null);
    Contract.Requires(cce.NonNullElements(body));
    Body = body;
  }

  public override IEnumerable<Statement> SubStatements => Body;

  public virtual void AppendStmt(Statement s) {
    Contract.Requires(s != null);
    Body.Add(s);
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var braceIndent = indentBefore;
    var innerBlockIndent = indentBefore + formatter.SpaceTab;
    foreach (var token in OwnedTokens) {
      if (formatter.SetIndentLabelTokens(token, indentBefore)) {
        continue;
      }
      switch (token.val) {
        case "{": {
            if (!formatter.TryGetIndentInline(token, out var indentLineBefore)) {
              formatter.SetDelimiterIndentedRegions(token, braceIndent);
            } else {
              braceIndent = indentLineBefore;
              if (!formatter.TryGetIndentAbove(token, out _)) {
                formatter.SetDelimiterIndentedRegions(token, braceIndent);
              }

              if (!TokenNewIndentCollector.IsFollowedByNewline(token)) {
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

    foreach (var childStatement in Body) {
      if (childStatement is not BlockStmt or BlockByProofStmt && OwnedTokens.Any()) {
        formatter.SetIndentations(childStatement.StartToken, innerBlockIndent, innerBlockIndent);
      }

      formatter.Visit(childStatement, indentBefore + formatter.SpaceTab);
    }

    return false;
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext, string proofContext,
    bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    IsGhost = mustBeErasable;  // set .IsGhost before descending into substatements (since substatements may do a 'break' out of this block)
    if (this is DividedBlockStmt ds) {
      ds.BodyInit.ForEach(ss =>
        ss.ResolveGhostness(resolver, reporter, mustBeErasable, codeContext, proofContext, allowAssumptionVariables, true));
      ds.BodyProper.ForEach(ss =>
        ss.ResolveGhostness(resolver, reporter, mustBeErasable, codeContext, proofContext, allowAssumptionVariables,
          inConstructorInitializationPhase));
    } else {
      Body.ForEach(ss => ss.ResolveGhostness(resolver, reporter, mustBeErasable, codeContext, proofContext,
        allowAssumptionVariables, inConstructorInitializationPhase));
    }
    IsGhost = IsGhost || Body.All(ss => ss.IsGhost);  // mark the block statement as ghost if all its substatements are ghost
  }
}