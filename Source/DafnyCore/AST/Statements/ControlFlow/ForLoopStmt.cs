using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ForLoopStmt : OneBodyLoopStmt, ICloneable<ForLoopStmt>, ICanFormat {
  public readonly BoundVar LoopIndex;
  public readonly Expression Start;
  public readonly Expression/*?*/ End;
  public readonly bool GoingUp;

  public ForLoopStmt Clone(Cloner cloner) {
    return new ForLoopStmt(cloner, this);
  }

  public ForLoopStmt(Cloner cloner, ForLoopStmt original) : base(cloner, original) {
    LoopIndex = cloner.CloneBoundVar(original.LoopIndex, false);
    Start = cloner.CloneExpr(original.Start);
    End = cloner.CloneExpr(original.End);
    GoingUp = original.GoingUp;
  }

  public ForLoopStmt(IOrigin rangeOrigin, BoundVar loopIndexVariable, Expression start, Expression/*?*/ end, bool goingUp,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt /*?*/ body, Attributes attrs)
    : base(rangeOrigin, invariants, decreases, mod, body, attrs) {
    Contract.Requires(rangeOrigin != null);
    Contract.Requires(loopIndexVariable != null);
    Contract.Requires(start != null);
    Contract.Requires(invariants != null);
    Contract.Requires(decreases != null);
    Contract.Requires(mod != null);
    LoopIndex = loopIndexVariable;
    Start = start;
    End = end;
    GoingUp = goingUp;
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      yield return Start;
      if (End != null) {
        yield return End;
      }
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var forReached = false;
    var specification = false;
    foreach (var token in OwnedTokens) {
      if (formatter.SetIndentLabelTokens(token, indentBefore)) {
        continue;
      }
      if (token.val == "for") {
        formatter.SetOpeningIndentedRegion(token, indentBefore);
        forReached = true;
        continue;
      }

      if (!forReached) {
        continue;
      }

      if (specification) {
        formatter.SetOpeningIndentedRegion(token, indentBefore + formatter.SpaceTab);
      }

      if (token.val is "to" or "downto") {
        specification = true;
      }
    }

    foreach (var ens in Invariants) {
      formatter.SetAttributedExpressionIndentation(ens, indentBefore + formatter.SpaceTab);
    }

    formatter.SetIndentBody(Body, indentBefore);
    formatter.SetClosingIndentedRegion(EndToken, indentBefore);
    return false;
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext, string proofContext,
    bool allowAssumptionVariables, bool inConstructorInitializationPhase) {

    var s = this;
    if (proofContext != null && s.Mod.Expressions != null && s.Mod.Expressions.Count != 0) {
      reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_loop_in_proof_may_not_use_modifies, s.Mod.Expressions[0].Tok, $"a loop in {proofContext} is not allowed to use 'modifies' clauses");
    }

    s.IsGhost = mustBeErasable || ExpressionTester.UsesSpecFeatures(s.Start) || (s.End != null && ExpressionTester.UsesSpecFeatures(s.End));
    if (!mustBeErasable && s.IsGhost) {
      reporter.Info(MessageSource.Resolver, s.Tok, "ghost for-loop");
    }
    if (s.IsGhost) {
      if (s.Decreases.Expressions.Exists(e => e is WildcardExpr)) {
        reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_decreases_forbidden_on_ghost_loops, s, "'decreases *' is not allowed on ghost loops");
      } else if (s.End == null && s.Decreases.Expressions.Count == 0) {
        reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_ghost_loop_must_terminate, s, "a ghost loop must be terminating; make the end-expression specific or add a 'decreases' clause");
      }
    }
    if (s.IsGhost && s.Mod.Expressions != null) {
      s.Mod.Expressions.ForEach(resolver.DisallowNonGhostFieldSpecifiers);
    }
    if (s.Body != null) {
      s.Body.ResolveGhostness(resolver, reporter, s.IsGhost, codeContext,
        proofContext, allowAssumptionVariables, inConstructorInitializationPhase);
      if (s.Body.IsGhost) {
        s.IsGhost = true;
      }
    }
    if (!s.IsGhost) {
      // If there were features in the bounds that are treated differently in ghost and non-ghost
      // contexts, make sure they get treated for non-ghost use.
      ExpressionTester.CheckIsCompilable(resolver, reporter, s.Start, codeContext);
      if (s.End != null) {
        ExpressionTester.CheckIsCompilable(resolver, reporter, s.End, codeContext);
      }
    }
  }
}
