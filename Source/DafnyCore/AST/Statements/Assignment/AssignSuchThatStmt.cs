using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Parsed from ":|"
/// </summary>
public class AssignSuchThatStmt : ConcreteAssignStatement, ICloneable<AssignSuchThatStmt>, ICanResolveNewAndOld {
  public Expression Expr;
  public AttributedToken AssumeToken;

  public override IEnumerable<INode> PreResolveChildren =>
    Lhss.Concat<Node>(new List<Node>() { Expr });

  [FilledInDuringResolution] public List<BoundedPool> Bounds;  // null for a ghost statement
  // invariant Bounds == null || Bounds.Count == BoundVars.Count;
  [FilledInDuringResolution] public List<IVariable> MissingBounds;  // remains "null" if bounds can be found
  // invariant Bounds == null || MissingBounds == null;
  public class WiggleWaggleBound : BoundedPool {
    public override PoolVirtues Virtues => PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
    public override int Preference() => 1;
    public override BoundedPool Clone(Cloner cloner) {
      return this;
    }
  }

  public override IEnumerable<IdentifierExpr> GetAssignedLocals() {
    return Lhss.Select(lhs => lhs.Resolved).OfType<IdentifierExpr>();
  }

  public override IEnumerable<INode> Children => Lhss.Concat<Node>(new[] { Expr });

  public AssignSuchThatStmt Clone(Cloner cloner) {
    return new AssignSuchThatStmt(cloner, this);
  }

  public AssignSuchThatStmt(Cloner cloner, AssignSuchThatStmt original) : base(cloner, original) {
    Expr = cloner.CloneExpr(original.Expr);
    AssumeToken = cloner.AttributedTok(original.AssumeToken);

    if (cloner.CloneResolvedFields) {
      Bounds = original.Bounds?.Select(bp => bp.Clone(cloner)).ToList();
      MissingBounds = original.MissingBounds?.Select(v => cloner.CloneIVariable(v, true)).ToList();
    }
  }

  /// <summary>
  /// "assumeToken" is allowed to be "null", in which case the verifier will check that a RHS value exists.
  /// If "assumeToken" is non-null, then it should denote the "assume" keyword used in the statement.
  /// </summary>
  public AssignSuchThatStmt(IOrigin origin, List<Expression> lhss, Expression expr, AttributedToken assumeToken, Attributes attributes)
    : base(origin, lhss, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(Cce.NonNullElements(lhss));
    Contract.Requires(lhss.Count != 0);
    Contract.Requires(expr != null);
    Expr = expr;
    if (assumeToken != null) {
      AssumeToken = assumeToken;
    }
  }
  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      yield return Expr;
    }
  }

  public override void GenResolve(INewOrOldResolver resolver, ResolutionContext resolutionContext) {
    Contract.Requires(this != null);
    Contract.Requires(resolutionContext != null);

    if (!resolutionContext.IsGhost && resolver.Options.ForbidNondeterminism) {
      resolver.Reporter.Error(MessageSource.Resolver, GeneratorErrors.ErrorId.c_assign_such_that_forbidden, Origin,
        "assign-such-that statement forbidden by the --enforce-determinism option");
    }
    base.GenResolve(resolver, resolutionContext);

    if (AssumeToken != null) {
      if (!resolver.Options.Get(CommonOptionBag.AllowAxioms) && !AssumeToken.IsExplicitAxiom()) {
        resolver.Reporter.Warning(MessageSource.Resolver, "", AssumeToken.Token,
          "assume keyword in assign-such-that statement has no {:axiom} annotation");
      }

      resolver.ResolveAttributes(AssumeToken, resolutionContext);
    }

    var lhsSimpleVariables = new HashSet<IVariable>();
    foreach (var lhs in Lhss) {
      if (lhs.Resolved != null) {
        resolver.CheckIsLvalue(lhs.Resolved, resolutionContext);
      } else {
        Contract.Assert(resolver.Reporter.HasErrors);
      }
      if (lhs.Resolved is IdentifierExpr ide) {
        if (!lhsSimpleVariables.Add(ide.Var)) {
          // syntactically forbid duplicate simple-variables on the LHS
          resolver.Reporter.Error(MessageSource.Resolver, lhs, $"variable '{ide.Var.Name}' occurs more than once as left-hand side of :|");
        }
      }
      // to ease in the verification of the existence check, only allow local variables as LHSs
      if (AssumeToken == null && !(lhs.Resolved is IdentifierExpr)) {
        resolver.Reporter.Error(MessageSource.Resolver, lhs, "an assign-such-that statement (without an 'assume' clause) currently only supports local-variable LHSs");
      }
    }

    resolver.ResolveExpression(Expr, resolutionContext);
    resolver.ConstrainTypeExprBool(Expr, "type of RHS of assign-such-that statement must be boolean (got {0})");
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext,
    string proofContext, bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    IsGhost = mustBeErasable || AssumeToken != null || Lhss.Any(SingleAssignStmt.LhsIsToGhost);
    if (mustBeErasable && !codeContext.IsGhost) {
      foreach (var lhs in Lhss) {
        var gk = SingleAssignStmt.LhsIsToGhost_Which(lhs);
        if (gk != SingleAssignStmt.NonGhostKind.IsGhost) {
          reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_no_assign_to_var_in_ghost, lhs,
            "cannot assign to {0} in a ghost context", SingleAssignStmt.NonGhostKind_To_String(gk));
        }
      }
    } else if (!mustBeErasable && AssumeToken == null && ExpressionTester.UsesSpecFeatures(Expr)) {
      foreach (var lhs in Lhss) {
        var gk = SingleAssignStmt.LhsIsToGhost_Which(lhs);
        if (gk != SingleAssignStmt.NonGhostKind.IsGhost) {
          reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_no_assign_ghost_to_var, lhs,
            "{0} cannot be assigned a value that depends on a ghost", SingleAssignStmt.NonGhostKind_To_String(gk));
        }
      }
    }
  }
}
