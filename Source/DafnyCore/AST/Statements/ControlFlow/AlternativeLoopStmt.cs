using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class AlternativeLoopStmt : LoopStmt, ICloneable<AlternativeLoopStmt>, ICanFormat {
  public bool UsesOptionalBraces;
  public List<GuardedAlternative> Alternatives;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Alternatives != null);
  }

  public new AlternativeLoopStmt Clone(Cloner cloner) {
    return new AlternativeLoopStmt(cloner, this);
  }

  public AlternativeLoopStmt(Cloner cloner, AlternativeLoopStmt original) : base(cloner, original) {
    Alternatives = original.Alternatives.ConvertAll(cloner.CloneGuardedAlternative);
    UsesOptionalBraces = original.UsesOptionalBraces;
  }

  public AlternativeLoopStmt(IOrigin origin,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    List<GuardedAlternative> alternatives, bool usesOptionalBraces)
    : base(origin, invariants, decreases, mod) {
    Contract.Requires(alternatives != null);
    this.Alternatives = alternatives;
    this.UsesOptionalBraces = usesOptionalBraces;
  }
  public AlternativeLoopStmt(IOrigin origin,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    List<GuardedAlternative> alternatives, bool usesOptionalBraces, List<Label> labels, Attributes attributes)
    : base(origin, invariants, decreases, mod, labels, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(alternatives != null);
    this.Alternatives = alternatives;
    this.UsesOptionalBraces = usesOptionalBraces;
  }
  public override IEnumerable<Statement> SubStatements {
    get {
      foreach (var alt in Alternatives) {
        foreach (var s in alt.Body) {
          yield return s;
        }
      }
    }
  }

  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      foreach (var alt in Alternatives) {
        foreach (var e in Attributes.SubExpressions(alt.Attributes)) {
          yield return e;
        }
      }
    }
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      foreach (var alt in Alternatives) {
        yield return alt.Guard;
      }
    }
  }

  public override IEnumerable<INode> Children => SpecificationSubExpressions.Concat<Node>(Alternatives);
  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentCases(indentBefore, OwnedTokens.Concat(Alternatives.SelectMany(alternative => alternative.OwnedTokens)), () => {
      foreach (var ens in Invariants) {
        formatter.SetAttributedExpressionIndentation(ens, indentBefore + formatter.SpaceTab);
      }

      foreach (var dec in Decreases.Expressions) {
        formatter.SetDecreasesExpressionIndentation(dec, indentBefore + formatter.SpaceTab);
      }

      formatter.VisitAlternatives(Alternatives, indentBefore);
      if (EndToken.val == "}") {
        formatter.SetClosingIndentedRegion(EndToken, indentBefore);
      }
    });
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext, string proofContext,
    bool allowAssumptionVariables, bool inConstructorInitializationPhase) {

    var s = this;
    if (proofContext != null && s.Mod.Expressions != null && s.Mod.Expressions.Count != 0) {
      reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_loop_in_proof_may_not_use_modifies, s.Mod.Expressions[0].Origin, $"a loop in {proofContext} is not allowed to use 'modifies' clauses");
    }

    s.IsGhost = mustBeErasable || s.Alternatives.Exists(alt => ExpressionTester.UsesSpecFeatures(alt.Guard));
    if (!mustBeErasable && s.IsGhost) {
      reporter.Info(MessageSource.Resolver, s.Origin, "ghost while");
    }
    if (s.IsGhost && s.Decreases.Expressions.Exists(e => e is WildcardExpr)) {
      reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_decreases_forbidden_on_ghost_loops, s, "'decreases *' is not allowed on ghost loops");
    }
    if (s.IsGhost && s.Mod.Expressions != null) {
      s.Mod.Expressions.ForEach(resolver.DisallowNonGhostFieldSpecifiers);
    }

    s.Alternatives.ForEach(alt => alt.Body.ForEach(ss =>
      ss.ResolveGhostness(resolver, reporter, s.IsGhost, codeContext,
      proofContext, allowAssumptionVariables, inConstructorInitializationPhase)));
    s.IsGhost = s.IsGhost || (!s.Decreases.Expressions.Exists(e => e is WildcardExpr) && s.Alternatives.All(alt => alt.Body.All(ss => ss.IsGhost)));
    if (!s.IsGhost) {
      // If there were features in the guards that are treated differently in ghost and non-ghost
      // contexts, make sure they get treated for non-ghost use.
      foreach (var alt in s.Alternatives) {
        ExpressionTester.CheckIsCompilable(resolver, reporter, alt.Guard, codeContext);
      }
    }
  }
}