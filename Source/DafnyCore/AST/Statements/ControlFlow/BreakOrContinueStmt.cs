#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

/// <summary>
/// Class "BreakStmt" represents both "break" and "continue" statements.
/// </summary>
public class BreakOrContinueStmt : Statement, IHasReferences, ICloneable<BreakOrContinueStmt> {
  public Name? TargetLabel;
  public bool IsContinue;
  public string Kind => IsContinue ? "continue" : "break";
  public int BreakAndContinueCount;
  [FilledInDuringResolution] public LabeledStatement TargetStmt = null!;
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
      TargetStmt = (LabeledStatement)cloner.CloneStmt(original.TargetStmt, true);
    }
  }

  [SyntaxConstructor]
  public BreakOrContinueStmt(IOrigin origin, Name? targetLabel, int breakAndContinueCount, bool isContinue, Attributes? attributes = null)
    : base(origin, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(targetLabel != null);
    TargetLabel = targetLabel;
    BreakAndContinueCount = breakAndContinueCount;
    IsContinue = isContinue;
  }

  /// <summary>
  /// For "isContinue == false", represents the statement "break ^breakAndContinueCount ;".
  /// For "isContinue == true", represents the statement "break ^(breakAndContinueCount - 1) continue;".
  /// </summary>
  public BreakOrContinueStmt(IOrigin origin, int breakAndContinueCount, bool isContinue, Attributes? attributes = null)
    : base(origin, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(1 <= breakAndContinueCount);
    BreakAndContinueCount = breakAndContinueCount;
    IsContinue = isContinue;
  }

  public IEnumerable<Reference> GetReferences() {
    return TargetStmt is IHasNavigationToken target ? new[] {
      new Reference(TargetLabel == null ? ReportingRange : TargetLabel.EntireRange, target)
    } : Enumerable.Empty<Reference>();
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext,
    string? proofContext, bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    IsGhost = mustBeErasable;
    if (IsGhost && !TargetStmt.IsGhost) {
      var targetKind = TargetStmt is LoopStmt ? "loop" : "structure";
      reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_ghost_break, this,
        $"ghost-context {Kind} statement is not allowed to {Kind} out of non-ghost {targetKind}");
    }
  }
}