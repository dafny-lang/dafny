using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Class "BreakStmt" represents both "break" and "continue" statements.
/// </summary>
public class BreakOrContinueStmt : Statement, IHasReferences, ICloneable<BreakOrContinueStmt> {
  public readonly Token TargetLabel;
  public readonly bool IsContinue;
  public string Kind => IsContinue ? "continue" : "break";
  public readonly int BreakAndContinueCount;
  [FilledInDuringResolution] public Statement TargetStmt;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(TargetLabel != null || 1 <= BreakAndContinueCount);
  }

  public BreakOrContinueStmt Clone(Cloner cloner) {
    return new BreakOrContinueStmt(cloner, this);
  }

  public BreakOrContinueStmt(Cloner cloner, BreakOrContinueStmt original) : base(cloner, original) {
    TargetLabel = original.TargetLabel;
    IsContinue = original.IsContinue;
    BreakAndContinueCount = original.BreakAndContinueCount;
    if (cloner.CloneResolvedFields) {
      TargetStmt = cloner.CloneStmt(original.TargetStmt, true);
    }
  }

  public BreakOrContinueStmt(IOrigin origin, Token targetLabel, bool isContinue, Attributes attributes = null)
    : base(origin, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(targetLabel != null);
    TargetLabel = targetLabel;
    IsContinue = isContinue;
  }

  /// <summary>
  /// For "isContinue == false", represents the statement "break ^breakAndContinueCount ;".
  /// For "isContinue == true", represents the statement "break ^(breakAndContinueCount - 1) continue;".
  /// </summary>
  public BreakOrContinueStmt(IOrigin origin, int breakAndContinueCount, bool isContinue, Attributes attributes = null)
    : base(origin, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(1 <= breakAndContinueCount);
    BreakAndContinueCount = breakAndContinueCount;
    IsContinue = isContinue;
  }

  public IEnumerable<Reference> GetReferences() {
    return TargetStmt is IHasNavigationToken target ? new[] {
      new Reference(TargetLabel != null ? new TokenRange(TargetLabel, TargetLabel) : ReportingRange, target)
    } : Enumerable.Empty<Reference>();
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext,
    string proofContext, bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    IsGhost = mustBeErasable;
    if (IsGhost && !TargetStmt.IsGhost) {
      var targetKind = TargetStmt is LoopStmt ? "loop" : "structure";
      reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_ghost_break, this,
        $"ghost-context {Kind} statement is not allowed to {Kind} out of non-ghost {targetKind}");
    }
  }
}