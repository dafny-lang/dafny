using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Dafny.Auditor;

namespace Microsoft.Dafny;

public class ForallStmt : Statement, ICloneable<ForallStmt>, ICanFormat {
  public List<BoundVar> BoundVars;  // note, can be the empty list, in which case Range denotes "true"
  public Expression Range;  // mostly readonly, except that it may in some cases be updated during resolution to conjoin the precondition of the call in the body
  public List<AttributedExpression> Ens;
  public Statement Body;
  [FilledInDuringResolution]
  public List<Expression> EffectiveEnsuresClauses;   // fill in by rewriter.
  public bool CanConvert = true; //  can convert to ForallExpressions

  [FilledInDuringResolution] public List<BoundedPool> Bounds;
  // invariant: if successfully resolved, Bounds.Count == BoundVars.Count;

  /// <summary>
  /// Assign means there are no ensures clauses and the body consists of one update statement,
  ///   either to an object field or to an array.
  /// Call means there are no ensures clauses and the body consists of a single call to a (presumably
  ///   ghost, but non-ghost is also allowed) method with no out-parameters and an empty modifies
  ///   clause.
  /// Proof means there is at least one ensures clause, and the body consists of any (presumably ghost,
  ///   but non-ghost is also allowed) code without side effects on variables (including fields and array
  ///   elements) declared outside the body itself.
  /// Notes:
  /// * More kinds may be allowed in the future.
  /// * One could also allow Call to call non-ghost methods without side effects.  However, that
  ///   would seem pointless in the program, so they are disallowed (to avoid any confusion that
  ///   such use of the forall statement might actually have a point).
  /// * One could allow Proof even without ensures clauses that "export" what was learned.
  ///   However, that might give the false impression that the body is nevertheless exported.
  /// </summary>
  public enum BodyKind { Assign, Call, Proof }
  [FilledInDuringResolution] public BodyKind Kind;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(BoundVars != null);
    Contract.Invariant(Range != null);
    Contract.Invariant(BoundVars.Count != 0 || LiteralExpr.IsTrue(Range));
    Contract.Invariant(Ens != null);
  }

  public ForallStmt Clone(Cloner cloner) {
    return new ForallStmt(cloner, this);
  }

  public ForallStmt(Cloner cloner, ForallStmt original) : base(cloner, original) {
    BoundVars = original.BoundVars.ConvertAll(bv => cloner.CloneBoundVar(bv, false));
    Range = cloner.CloneExpr(original.Range);
    Ens = original.Ens.Select(cloner.CloneAttributedExpr).ToList();
    Body = cloner.CloneStmt(original.Body, false);
    Attributes = cloner.CloneAttributes(original.Attributes);

    if (cloner.CloneResolvedFields) {
      Bounds = original.Bounds.ConvertAll(bp => bp?.Clone(cloner));
      Kind = original.Kind;
      EffectiveEnsuresClauses = original.EffectiveEnsuresClauses?.Select(cloner.CloneExpr).ToList();
    }
  }

  public ForallStmt(IOrigin origin, List<BoundVar> boundVars, Attributes attributes, Expression range, List<AttributedExpression> ens, Statement body)
    : base(origin, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(cce.NonNullElements(boundVars));
    Contract.Requires(range != null);
    Contract.Requires(boundVars.Count != 0 || LiteralExpr.IsTrue(range));
    Contract.Requires(cce.NonNullElements(ens));
    BoundVars = boundVars;
    Range = range;
    Ens = ens;
    Body = body;
  }

  public Statement S0 {
    get {
      // dig into Body to find a single statement
      Statement s = Body;
      while (true) {
        if (s is BlockStmt { Body: { Count: 1 } } block) {
          s = block.Body[0];
          // dig further into s
        } else if (s is AssignStatement update) {
          if (update.ResolvedStatements?.Count == 1) {
            s = update.ResolvedStatements[0];
            // dig further into s
          } else {
            return s;
          }
        } else {
          return s;
        }
      }
    }
  }

  public override IEnumerable<Statement> SubStatements {
    get {
      if (Body != null) {
        yield return Body;
      }
    }
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) {
        yield return e;
      }

      yield return Range;
    }
  }
  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) {
        yield return e;
      }
      foreach (var ee in Ens) {
        foreach (var e in Attributes.SubExpressions(ee.Attributes)) { yield return e; }
        yield return ee.E;
      }

      if (EffectiveEnsuresClauses != null) {
        foreach (var e in EffectiveEnsuresClauses) {
          yield return e;
        }
      }
    }
  }

  public override IEnumerable<Assumption> Assumptions(Declaration decl) {
    if (Body is null) {
      yield return new Assumption(decl, Origin, AssumptionDescription.ForallWithoutBody);
    }
  }

  public List<BoundVar> UncompilableBoundVars() {
    Contract.Ensures(Contract.Result<List<BoundVar>>() != null);
    var v = BoundedPool.PoolVirtues.Finite | BoundedPool.PoolVirtues.Enumerable;
    return BoundedPool.MissingBounds(BoundVars, Bounds, v);
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    formatter.SetIndentLikeLoop(OwnedTokens, Body, indentBefore);
    if (Range != null) {
      formatter.Visit(Range, indentBefore + formatter.SpaceTab);
    }
    foreach (var ens in Ens) {
      formatter.SetAttributedExpressionIndentation(ens, indentBefore + formatter.SpaceTab);
    }

    formatter.SetClosingIndentedRegion(EndToken, indentBefore);
    return false;
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext, string proofContext,
    bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    IsGhost = mustBeErasable || Kind != BodyKind.Assign || ExpressionTester.UsesSpecFeatures(Range);
    if (proofContext != null && Kind == BodyKind.Assign) {
      reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_no_aggregate_heap_update_in_proof, this, $"{proofContext} is not allowed to perform an aggregate heap update");
    } else if (Body != null) {
      Body.ResolveGhostness(resolver, reporter, IsGhost, codeContext,
        Kind == BodyKind.Assign ? proofContext : "a forall statement", allowAssumptionVariables, inConstructorInitializationPhase);
    }
    IsGhost = IsGhost || Body == null || Body.IsGhost;

    if (!IsGhost) {
      // Since we've determined this is a non-ghost forall statement, we now check that the bound variables have compilable bounds.
      var uncompilableBoundVars = UncompilableBoundVars();
      if (uncompilableBoundVars.Count != 0) {
        foreach (var bv in uncompilableBoundVars) {
          reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_unknown_bounds_for_forall, this, "forall statements in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce or compile a bounded set of values for '{0}'", bv.Name);
        }
      }

      // If there were features in the range that are treated differently in ghost and non-ghost
      // contexts, make sure they get treated for non-ghost use.
      ExpressionTester.CheckIsCompilable(resolver, reporter, Range, codeContext);
    }
  }
}
