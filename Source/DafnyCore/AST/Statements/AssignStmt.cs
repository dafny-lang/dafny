using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class AssignStmt : Statement, ICloneable<AssignStmt> {
  public readonly Expression Lhs;
  public readonly AssignmentRhs Rhs;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Lhs != null);
    Contract.Invariant(Rhs != null);
  }

  public override IToken Tok {
    get {
      var previous = Rhs.StartToken.Prev;
      // If there was a single assignment, report on the operator.
      var singleAssignment = previous.val == ":="; 
      // If there was an implicit return assignment, report on the return
      var implicitAssignment = previous.val == "return";
      if (singleAssignment || implicitAssignment) {
        return previous;
      }
      return Rhs.StartToken;
    }
  }

  public override IEnumerable<Node> Children => new Node[] { Lhs, Rhs };

  public AssignStmt Clone(Cloner cloner) {
    return new AssignStmt(cloner, this);
  }

  public AssignStmt(Cloner cloner, AssignStmt original) : base(cloner, original) {
    Lhs = cloner.CloneExpr(original.Lhs);
    Rhs = cloner.CloneRHS(original.Rhs);
  }

  public AssignStmt(RangeToken rangeToken, Expression lhs, AssignmentRhs rhs)
    : base(rangeToken) {
    Contract.Requires(rangeToken != null);
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