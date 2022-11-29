using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ForallStmt : Statement {
  public readonly List<BoundVar> BoundVars;  // note, can be the empty list, in which case Range denotes "true"
  public Expression Range;  // mostly readonly, except that it may in some cases be updated during resolution to conjoin the precondition of the call in the body
  public readonly List<AttributedExpression> Ens;
  public readonly Statement Body;
  public List<Expression> ForallExpressions;   // fill in by rewriter.
  public bool CanConvert = true; //  can convert to ForallExpressions

  [FilledInDuringResolution] public List<ComprehensionExpr.BoundedPool> Bounds;
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

  public ForallStmt(IToken tok, IToken endTok, List<BoundVar> boundVars, Attributes attrs, Expression range, List<AttributedExpression> ens, Statement body)
    : base(tok, endTok, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(cce.NonNullElements(boundVars));
    Contract.Requires(range != null);
    Contract.Requires(boundVars.Count != 0 || LiteralExpr.IsTrue(range));
    Contract.Requires(cce.NonNullElements(ens));
    this.BoundVars = boundVars;
    this.Range = range;
    this.Ens = ens;
    this.Body = body;
  }

  public Statement S0 {
    get {
      // dig into Body to find a single statement
      Statement s = this.Body;
      while (true) {
        var block = s as BlockStmt;
        if (block != null && block.Body.Count == 1) {
          s = block.Body[0];
          // dig further into s
        } else if (s is UpdateStmt) {
          var update = (UpdateStmt)s;
          if (update.ResolvedStatements.Count == 1) {
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
    }
  }

  public List<BoundVar> UncompilableBoundVars() {
    Contract.Ensures(Contract.Result<List<BoundVar>>() != null);
    var v = ComprehensionExpr.BoundedPool.PoolVirtues.Finite | ComprehensionExpr.BoundedPool.PoolVirtues.Enumerable;
    return ComprehensionExpr.BoundedPool.MissingBounds(BoundVars, Bounds, v);
  }
}