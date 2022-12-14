using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class AssignStmt : Statement {
  public readonly Expression Lhs;
  public readonly AssignmentRhs Rhs;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Lhs != null);
    Contract.Invariant(Rhs != null);
  }

  public AssignStmt(IToken tok, IToken endTok, Expression lhs, AssignmentRhs rhs)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(lhs != null);
    Contract.Requires(rhs != null);
    this.Lhs = lhs;
    this.Rhs = rhs;
  }

  public override IEnumerable<Statement> SubStatements {
    get {
      foreach (var s in Rhs.SubStatements) {
        yield return s;
      }
    }
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      yield return Lhs;
      foreach (var ee in Rhs.NonSpecificationSubExpressions) {
        yield return ee;
      }
    }
  }

  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      foreach (var ee in Rhs.SpecificationSubExpressions) {
        yield return ee;
      }
    }
  }

  /// <summary>
  /// This method assumes "lhs" has been successfully resolved.
  /// </summary>
  public static bool LhsIsToGhost(Expression lhs) {
    Contract.Requires(lhs != null);
    return LhsIsToGhost_Which(lhs) == NonGhostKind.IsGhost;
  }
  public static bool LhsIsToGhostOrAutoGhost(Expression lhs) {
    Contract.Requires(lhs != null);
    return LhsIsToGhost_Which(lhs) == NonGhostKind.IsGhost || lhs.Resolved is AutoGhostIdentifierExpr;
  }
  public enum NonGhostKind { IsGhost, Variable, Field, ArrayElement }
  public static string NonGhostKind_To_String(NonGhostKind gk) {
    Contract.Requires(gk != NonGhostKind.IsGhost);
    switch (gk) {
      case NonGhostKind.Variable: return "non-ghost variable";
      case NonGhostKind.Field: return "non-ghost field";
      case NonGhostKind.ArrayElement: return "array element";
      default:
        Contract.Assume(false);  // unexpected NonGhostKind
        throw new cce.UnreachableException();  // please compiler
    }
  }
  /// <summary>
  /// This method assumes "lhs" has been successfully resolved.
  /// </summary>
  public static NonGhostKind LhsIsToGhost_Which(Expression lhs) {
    Contract.Requires(lhs != null);
    lhs = lhs.Resolved;
    if (lhs is AutoGhostIdentifierExpr) {
      // TODO: Should we return something different for this case?
      var x = (IdentifierExpr)lhs;
      if (!x.Var.IsGhost) {
        return NonGhostKind.Variable;
      }
    } else if (lhs is IdentifierExpr) {
      var x = (IdentifierExpr)lhs;
      if (!x.Var.IsGhost) {
        return NonGhostKind.Variable;
      }
    } else if (lhs is MemberSelectExpr) {
      var x = (MemberSelectExpr)lhs;
      if (!x.Member.IsGhost) {
        return NonGhostKind.Field;
      }
    } else {
      // LHS denotes an array element, which is always non-ghost
      return NonGhostKind.ArrayElement;
    }
    return NonGhostKind.IsGhost;
  }
}