using System.Diagnostics.Contracts;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

class FindFriendlyCalls_Visitor : ResolverTopDownVisitor<Resolver.CallingPosition> {
  public readonly bool IsCoContext;
  public readonly bool ContinuityIsImportant;
  public FindFriendlyCalls_Visitor(ErrorReporter reporter, bool co, bool continuityIsImportant)
    : base(reporter) {
    Contract.Requires(reporter != null);
    this.IsCoContext = co;
    this.ContinuityIsImportant = continuityIsImportant;
  }

  protected override bool VisitOneExpr(Expression expr, ref Resolver.CallingPosition cp) {
    if (expr is UnaryOpExpr) {
      var e = (UnaryOpExpr)expr;
      if (e.Op == UnaryOpExpr.Opcode.Not) {
        // for the sub-parts, use Invert(cp)
        cp = Resolver.Invert(cp);
        return true;
      }
    } else if (expr is BinaryExpr) {
      var e = (BinaryExpr)expr;
      switch (e.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.And:
        case BinaryExpr.ResolvedOpcode.Or:
          return true;  // do the sub-parts with the same "cp"
        case BinaryExpr.ResolvedOpcode.Imp:
          Visit(e.E0, Resolver.Invert(cp));
          Visit(e.E1, cp);
          return false;  // don't recurse (again) on the sub-parts
        default:
          break;
      }
    } else if (expr is NestedMatchExpr) {
      var e = (NestedMatchExpr)expr;
      Visit(e.Source, Resolver.CallingPosition.Neither);
      var theCp = cp;
      e.Cases.Iter(kase => Visit((Expression)kase.Body, theCp));
      return false;
    } else if (expr is MatchExpr) {
      var e = (MatchExpr)expr;
      Visit(e.Source, Resolver.CallingPosition.Neither);
      var theCp = cp;
      e.Cases.Iter(kase => Visit(kase.Body, theCp));
      return false;
    } else if (expr is ITEExpr) {
      var e = (ITEExpr)expr;
      Visit(e.Test, Resolver.CallingPosition.Neither);
      Visit(e.Thn, cp);
      Visit(e.Els, cp);
      return false;
    } else if (expr is LetExpr) {
      var e = (LetExpr)expr;
      foreach (var rhs in e.RHSs) {
        Visit(rhs, Resolver.CallingPosition.Neither);
      }
      var cpBody = cp;
      if (!e.Exact) {
        // a let-such-that expression introduces an existential that may depend on the _k in a least/greatest predicate, so we disallow recursive calls in the body of the let-such-that
        if (IsCoContext && cp == Resolver.CallingPosition.Positive) {
          cpBody = Resolver.CallingPosition.Neither;
        } else if (!IsCoContext && cp == Resolver.CallingPosition.Negative) {
          cpBody = Resolver.CallingPosition.Neither;
        }
      }
      Visit(e.Body, cpBody);
      return false;
    } else if (expr is QuantifierExpr) {
      var e = (QuantifierExpr)expr;
      Contract.Assert(e.SplitQuantifier == null); // No split quantifiers during resolution
      var cpos = IsCoContext ? cp : Resolver.Invert(cp);
      if (ContinuityIsImportant) {
        if ((cpos == Resolver.CallingPosition.Positive && e is ExistsExpr) || (cpos == Resolver.CallingPosition.Negative && e is ForallExpr)) {
          if (e.Bounds.Exists(bnd => bnd == null || (bnd.Virtues & ComprehensionExpr.BoundedPool.PoolVirtues.Finite) == 0)) {
            // To ensure continuity of extreme predicates, don't allow calls under an existential (resp. universal) quantifier
            // for greatest (resp. least) predicates).
            cp = Resolver.CallingPosition.Neither;
          }
        }
      }
      Visit(e.LogicalBody(), cp);
      return false;
    } else if (expr is StmtExpr) {
      var e = (StmtExpr)expr;
      Visit(e.E, cp);
      Visit(e.S, Resolver.CallingPosition.Neither);
      return false;
    } else if (expr is ConcreteSyntaxExpression) {
      // do the sub-parts with the same "cp"
      return true;
    }
    // do the sub-parts with cp := Neither
    cp = Resolver.CallingPosition.Neither;
    return true;
  }
}