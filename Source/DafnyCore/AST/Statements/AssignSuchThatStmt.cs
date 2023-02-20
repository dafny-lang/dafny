using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class AssignSuchThatStmt : ConcreteUpdateStatement, ICloneable<AssignSuchThatStmt>, ICanResolve {
  public readonly Expression Expr;
  public readonly AttributedToken AssumeToken;

  public override IToken Tok {
    get {
      var result = Expr.StartToken.Prev;
      if (char.IsLetter(result.val[0])) {
        // Jump to operator if we're on an assume keyword.
        result = result.Prev;
      }
      return result;
    }
  }

  [FilledInDuringResolution] public List<ComprehensionExpr.BoundedPool> Bounds;  // null for a ghost statement
  // invariant Bounds == null || Bounds.Count == BoundVars.Count;
  [FilledInDuringResolution] public List<IVariable> MissingBounds;  // remains "null" if bounds can be found
  // invariant Bounds == null || MissingBounds == null;
  public class WiggleWaggleBound : ComprehensionExpr.BoundedPool {
    public override PoolVirtues Virtues => PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
    public override int Preference() => 1;
    public override ComprehensionExpr.BoundedPool Clone(Cloner cloner) {
      return this;
    }
  }

  public override IEnumerable<Node> Children => Lhss.Concat<Node>(new[] { Expr });

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
  public AssignSuchThatStmt(RangeToken rangeToken, List<Expression> lhss, Expression expr, AttributedToken assumeToken, Attributes attrs)
    : base(rangeToken, lhss, attrs) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(cce.NonNullElements(lhss));
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

  public override void Resolve(Resolver resolver, ResolutionContext resolutionContext) {
    Contract.Requires(this != null);
    Contract.Requires(resolutionContext != null);

    base.Resolve(resolver, resolutionContext);

    if (AssumeToken != null) {
      if (!resolver.Options.Get(CommonOptionBag.AllowAxioms) && !AssumeToken.IsExplicitAxiom()) {
        resolver.Reporter.Warning(MessageSource.Resolver, ErrorDetail.ErrorID.None, AssumeToken.Token, "assume keyword in assign-such-that statement has no {:axiom} annotation.");
      }

      resolver.ResolveAttributes(AssumeToken, resolutionContext);
    }

    var lhsSimpleVariables = new HashSet<IVariable>();
    foreach (var lhs in Lhss) {
      if (lhs.Resolved != null) {
        resolver.CheckIsLvalue(lhs.Resolved, resolutionContext);
      } else {
        Contract.Assert(resolver.reporter.ErrorCount > 0);
      }
      if (lhs.Resolved is IdentifierExpr ide) {
        if (lhsSimpleVariables.Contains(ide.Var)) {
          // syntactically forbid duplicate simple-variables on the LHS
          resolver.reporter.Error(MessageSource.Resolver, lhs, $"variable '{ide.Var.Name}' occurs more than once as left-hand side of :|");
        } else {
          lhsSimpleVariables.Add(ide.Var);
        }
      }
      // to ease in the verification of the existence check, only allow local variables as LHSs
      if (AssumeToken == null && !(lhs.Resolved is IdentifierExpr)) {
        resolver.reporter.Error(MessageSource.Resolver, lhs, "an assign-such-that statement (without an 'assume' clause) currently only supports local-variable LHSs");
      }
    }

    resolver.ResolveExpression(Expr, resolutionContext);
    resolver.ConstrainTypeExprBool(Expr, "type of RHS of assign-such-that statement must be boolean (got {0})");
  }
}
