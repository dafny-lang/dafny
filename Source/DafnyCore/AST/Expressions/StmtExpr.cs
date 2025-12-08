using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// A StmtExpr has the form S;E where S is a statement (from a restricted set) and E is an expression.
/// The expression S;E evaluates to whatever E evaluates to, but its well-formedness comes down to
/// executing S (which itself must be well-formed) and then checking the well-formedness of E.
/// </summary>
public class StmtExpr : Expression, ICanFormat, ICloneable<StmtExpr> {
  public Statement S;
  public Expression E;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(S != null);
    Contract.Invariant(E != null);
  }

  public StmtExpr(Cloner cloner, StmtExpr original) : base(cloner, original) {
    E = cloner.CloneExpr(original.E);
    S = cloner.CloneStmt(original.S, false);
  }

  public override IEnumerable<INode> Children => new Node[] { S, E };

  public StmtExpr(IOrigin origin, Statement stmt, Expression expr)
    : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(stmt != null);
    Contract.Requires(expr != null);
    S = stmt;
    E = expr;
  }
  public override IEnumerable<Expression> SubExpressions {
    get {
      // Note:  A StmtExpr is unusual in that it contains a statement.  For now, callers
      // of SubExpressions need to be aware of this and handle it specially.
      yield return E;
    }
  }

  public override IEnumerable<Expression> TerminalExpressions {
    get {
      foreach (var e in E.TerminalExpressions) {
        yield return e;
      }
    }
  }

  /// <summary>
  /// Returns a conclusion that S gives rise to, that is, something that is known after
  /// S is executed.
  /// This method should be called only after successful resolution of the expression.
  /// </summary>
  public Expression GetStatementConclusion() {
    return GetStatementConclusion(S);
  }

  private Expression GetStatementConclusion(Statement statement) {
    switch (statement) {
      // this is one place where we actually investigate what kind of statement .S is
      case PredicateStmt stmt:
        return stmt.Expr;
      case CalcStmt stmt:
        return stmt.Result;
      case ForallStmt:
        return CreateBoolLiteral(Origin, true);  // one could wrap a `forall` expression around the `ensures` clause, but "true" is conservative and much simpler :)
      case HideRevealStmt:
        return CreateBoolLiteral(Origin, true);  // one could use the definition axiom or the referenced labeled assertions, but "true" is conservative and much simpler :)
      case AssignStatement:
        return CreateBoolLiteral(Origin, true);  // one could use the postcondition of the method, suitably instantiated, but "true" is conservative and much simpler :)
      case BlockByProofStmt stmt:
        return GetStatementConclusion(stmt.Body);
      default:
        Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected statement
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    formatter.Visit(S, indentBefore);
    formatter.SetIndentations(S.EndToken, below: indentBefore);
    formatter.Visit(E, indentBefore);
    return false;
  }

  public StmtExpr Clone(Cloner cloner) {
    return new StmtExpr(cloner, this);
  }
}