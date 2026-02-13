#nullable enable
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

/// <summary>
/// Used to capture some shared behavior between DividedBlockStmt and BlockStmt
/// </summary>
public abstract class BlockLikeStmt : LabeledStatement, ICanFormat {
  public abstract IReadOnlyList<Statement> Body { get; }

  protected BlockLikeStmt(Cloner cloner, BlockLikeStmt original) : base(cloner, original) {
  }

  [SyntaxConstructor]
  protected BlockLikeStmt(IOrigin origin, List<Label> labels, Attributes? attributes) : base(origin, labels, attributes) {
  }

  public override IEnumerable<Statement> SubStatements => Body;

  public abstract void AppendStmt(Statement s);
  public abstract void Prepend(Statement s);

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
    ICodeContext codeContext, string? proofContext,
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