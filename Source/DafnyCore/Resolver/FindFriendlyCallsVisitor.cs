using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public enum CallingPosition { Positive, Negative, Neither }

class FindFriendlyCallsVisitor : ResolverTopDownVisitor<CallingPosition> {
  public readonly bool IsCoContext;
  public readonly bool ContinuityIsImportant;

  /// <summary>
  /// While visiting the body of a quantifier that enumerates a type which may involve an ORDINAL (see
  /// VisitOneExpr), the type in question; null otherwise. The calling position alone does not say why
  /// it became Neither, so a subvisitor that wants to explain that to the user reads this.
  /// </summary>
  protected Type EnumeratedOrdinalType { get; private set; }
  public FindFriendlyCallsVisitor(ErrorReporter reporter, bool co, bool continuityIsImportant)
    : base(reporter) {
    Contract.Requires(reporter != null);
    this.IsCoContext = co;
    this.ContinuityIsImportant = continuityIsImportant;
  }

  public void KNatMismatchError(IOrigin tok, string contextName, ExtremePredicate.KType contextK, ExtremePredicate.KType calleeK) {
    var hint = contextK == ExtremePredicate.KType.Unspecified ? string.Format(" (perhaps try declaring '{0}' as '{0}[nat]')", contextName) : "";
    reporter.Error(MessageSource.Resolver, tok,
      "this call does not type check, because the context uses a _k parameter of type {0} whereas the callee uses a _k parameter of type {1}{2}",
      contextK == ExtremePredicate.KType.Nat ? "nat" : "ORDINAL",
      calleeK == ExtremePredicate.KType.Nat ? "nat" : "ORDINAL",
      hint);
  }

  /// <summary>
  /// True if "bound" confines a variable to set-many values, so that a quantifier over it contributes
  /// set-many states however large the variable's type is. Used for the ORDINAL-indexed case in
  /// VisitOneExpr, where that is what matters; the nat-indexed case needs outright finiteness instead,
  /// since an existential over an infinite range is not continuous even when the range is a set.
  ///
  /// Enumerable is what says so. A range a compiler can enumerate is countable, hence a set, and the
  /// virtue holds for exactly the pools whose range comes from a value rather than from a type: the
  /// elements of a collection, the subsets of one, an integer interval, a single value. It does not
  /// hold for AllocFreeBoundedPool, whose range is the whole of the variable's type, nor for
  /// SuperSetBoundedPool, whose range is a power class when the element type is a proper class.
  /// Finite is in here only because a few pools carry it without Enumerable.
  /// </summary>
  static bool ConfinesToASetOfValues(BoundedPool /*?*/ bound) {
    return bound != null &&
           (bound.Virtues & (BoundedPool.PoolVirtues.Finite | BoundedPool.PoolVirtues.Enumerable)) != 0;
  }

  static CallingPosition Invert(CallingPosition cp) {
    switch (cp) {
      case CallingPosition.Positive: return CallingPosition.Negative;
      case CallingPosition.Negative: return CallingPosition.Positive;
      default: return CallingPosition.Neither;
    }
  }

  protected override bool VisitOneExpr(Expression expr, ref CallingPosition cp) {
    if (expr is UnaryOpExpr) {
      var e = (UnaryOpExpr)expr;
      if (e.Op == UnaryOpExpr.Opcode.Not) {
        // for the sub-parts, use Invert(cp)
        cp = Invert(cp);
        return true;
      }
    } else if (expr is BinaryExpr) {
      var e = (BinaryExpr)expr;
      switch (e.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.And:
        case BinaryExpr.ResolvedOpcode.Or:
          return true;  // do the sub-parts with the same "cp"
        case BinaryExpr.ResolvedOpcode.Imp:
          Visit(e.E0, Invert(cp));
          Visit(e.E1, cp);
          return false;  // don't recurse (again) on the sub-parts
        default:
          break;
      }
    } else if (expr is NestedMatchExpr) {
      var e = (NestedMatchExpr)expr;
      Visit(e.Source, CallingPosition.Neither);
      var theCp = cp;
      e.Cases.ForEach(kase => Visit((Expression)kase.Body, theCp));
      return false;
    } else if (expr is MatchExpr) {
      var e = (MatchExpr)expr;
      Visit(e.Source, CallingPosition.Neither);
      var theCp = cp;
      e.Cases.ForEach(kase => Visit(kase.Body, theCp));
      return false;
    } else if (expr is ITEExpr) {
      var e = (ITEExpr)expr;
      Visit(e.Test, CallingPosition.Neither);
      Visit(e.Thn, cp);
      Visit(e.Els, cp);
      return false;
    } else if (expr is LetExpr) {
      var e = (LetExpr)expr;
      foreach (var rhs in e.RHSs) {
        Visit(rhs, CallingPosition.Neither);
      }
      var cpBody = cp;
      if (!e.Exact) {
        // a let-such-that expression introduces an existential that may depend on the _k in a least/greatest predicate, so we disallow recursive calls in the body of the let-such-that
        if (IsCoContext && cp == CallingPosition.Positive) {
          cpBody = CallingPosition.Neither;
        } else if (!IsCoContext && cp == CallingPosition.Negative) {
          cpBody = CallingPosition.Neither;
        }
      }
      Visit(e.Body, cpBody);
      return false;
    } else if (expr is QuantifierExpr) {
      var e = (QuantifierExpr)expr;
      Contract.Assert(e.SplitQuantifier == null); // No split quantifiers during resolution
      var cpos = IsCoContext ? cp : Invert(cp);
      Type enumeratedOrdinalType = null;
      if ((cpos == CallingPosition.Positive && e is ExistsExpr) || (cpos == CallingPosition.Negative && e is ForallExpr)) {
        // This is the quantifier direction that does not distribute over the limits of the sequence of
        // approximations: an existential for a greatest predicate, a universal for a least one. Two
        // things can go wrong under one, depending on how the approximations are indexed.
        if (ContinuityIsImportant) {
          // Approximations indexed by nat close at omega only if the predicate is continuous, which
          // any unbounded variable of such a quantifier destroys, whatever its type. So don't allow
          // calls under an existential (resp. universal) quantifier for greatest (resp. least)
          // predicates.
          if (e.Bounds == null ||
              e.Bounds.Exists(bnd => bnd == null || (bnd.Virtues & BoundedPool.PoolVirtues.Finite) == 0)) {
            cp = CallingPosition.Neither;
          }
        } else {
          // Approximations indexed by ORDINAL need no continuity, because they may run past omega --
          // but only as far as the ordinal at which they close, which exists only if the states
          // reachable by unfolding the definition form a set. A variable ranging over a type that has
          // as many values as there are ordinals makes them a proper class instead, and then no
          // ORDINAL indexes the fixpoint: see dafny-lang/dafny#6522 and #6523, which proved "1 == 2"
          // this way.
          //
          // Here, unlike above, it must be one and the same variable that is unbounded and of such a
          // type. A variable confined to a finite range contributes set-many states whatever its type,
          // and an unbounded variable of a set-sized type contributes set-many states too.
          for (var i = 0; i < e.BoundVars.Count && enumeratedOrdinalType == null; i++) {
            var bound = e.Bounds == null ? null : e.Bounds[i];
            if (!ConfinesToASetOfValues(bound) && e.BoundVars[i].Type.MayInvolveOrdinal) {
              enumeratedOrdinalType = e.BoundVars[i].Type;
              cp = CallingPosition.Neither;
            }
          }
        }
      }
      // Record the reason for the body only, so that a call made Neither for some other reason
      // elsewhere is not explained in terms of this quantifier.
      var previouslyEnumerated = EnumeratedOrdinalType;
      EnumeratedOrdinalType = enumeratedOrdinalType ?? previouslyEnumerated;
      Visit(e.LogicalBody(), cp);
      EnumeratedOrdinalType = previouslyEnumerated;
      return false;
    } else if (expr is StmtExpr) {
      var e = (StmtExpr)expr;
      Visit(e.E, cp);
      Visit(e.S, CallingPosition.Neither);
      return false;
    } else if (expr is ConcreteSyntaxExpression) {
      // do the sub-parts with the same "cp"
      return true;
    }
    // do the sub-parts with cp := Neither
    cp = CallingPosition.Neither;
    return true;
  }
}