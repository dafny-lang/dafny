using System.Collections.Generic;

namespace Microsoft.Dafny;

public class WhileStmt : OneBodyLoopStmt, ICloneable<WhileStmt>, ICanFormat {
  public readonly Expression/*?*/ Guard;

  public class LoopBodySurrogate {
    public readonly List<IVariable> LocalLoopTargets;
    public readonly bool UsesHeap;

    public LoopBodySurrogate(List<IVariable> localLoopTargets, bool usesHeap) {
      LocalLoopTargets = localLoopTargets;
      UsesHeap = usesHeap;
    }
  }

  public WhileStmt Clone(Cloner cloner) {
    return new WhileStmt(cloner, this);
  }

  public WhileStmt(Cloner cloner, WhileStmt original) : base(cloner, original) {
    Guard = cloner.CloneExpr(original.Guard);
  }

  public WhileStmt(IOrigin rangeOrigin, Expression guard,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt body)
    : base(rangeOrigin, invariants, decreases, mod, body, null) {
    Guard = guard;
  }

  public WhileStmt(IOrigin rangeOrigin, Expression guard,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt body, Attributes attrs)
    : base(rangeOrigin, invariants, decreases, mod, body, attrs) {
    Guard = guard;
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      if (Guard != null) {
        yield return Guard;
      }
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    formatter.SetIndentLikeLoop(OwnedTokens, Body, indentBefore);
    foreach (var ens in Invariants) {
      formatter.SetAttributedExpressionIndentation(ens, indentBefore + formatter.SpaceTab);
    }

    foreach (var dec in Decreases.Expressions) {
      formatter.SetDecreasesExpressionIndentation(dec, indentBefore + formatter.SpaceTab);
    }

    if (EndToken.val == "}") {
      formatter.SetClosingIndentedRegion(EndToken, indentBefore);
    }

    return false;
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext, string proofContext,
    bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    if (proofContext != null && Mod.Expressions != null && Mod.Expressions.Count != 0) {
      reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_loop_may_not_use_modifies, Mod.Expressions[0].Tok, $"a loop in {proofContext} is not allowed to use 'modifies' clauses");
    }

    IsGhost = mustBeErasable || (Guard != null && ExpressionTester.UsesSpecFeatures(Guard));
    if (!mustBeErasable && IsGhost) {
      reporter.Info(MessageSource.Resolver, Tok, "ghost while");
    }
    if (IsGhost && Decreases.Expressions.Exists(e => e is WildcardExpr)) {
      reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_decreases_forbidden_on_ghost_loops, this, "'decreases *' is not allowed on ghost loops");
    }
    if (IsGhost && Mod.Expressions != null) {
      Mod.Expressions.ForEach(resolver.DisallowNonGhostFieldSpecifiers);
    }
    if (Body != null) {
      Body.ResolveGhostness(resolver, reporter, IsGhost, codeContext, proofContext, allowAssumptionVariables,
        inConstructorInitializationPhase);
      if (Body.IsGhost && !Decreases.Expressions.Exists(e => e is WildcardExpr)) {
        IsGhost = true;
      }
    }
    if (!IsGhost && Guard != null) {
      // If there were features in the guard that are treated differently in ghost and non-ghost
      // contexts, make sure they get treated for non-ghost use.
      ExpressionTester.CheckIsCompilable(resolver, reporter, Guard, codeContext);
    }
  }
}