using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class IfStmt : Statement {
  public readonly bool IsBindingGuard;
  public readonly Expression Guard;
  public readonly BlockStmt Thn;
  public readonly Statement Els;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(!IsBindingGuard || (Guard is ExistsExpr && ((ExistsExpr)Guard).Range == null));
    Contract.Invariant(Thn != null);
    Contract.Invariant(Els == null || Els is BlockStmt || Els is IfStmt || Els is SkeletonStatement);
  }
  public IfStmt(IToken tok, IToken endTok, bool isBindingGuard, Expression guard, BlockStmt thn, Statement els)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
    Contract.Requires(thn != null);
    Contract.Requires(els == null || els is BlockStmt || els is IfStmt || els is SkeletonStatement);
    this.IsBindingGuard = isBindingGuard;
    this.Guard = guard;
    this.Thn = thn;
    this.Els = els;
  }
  public IfStmt(IToken tok, IToken endTok, bool isBindingGuard, Expression guard, BlockStmt thn, Statement els, Attributes attrs)
    : base(tok, endTok, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
    Contract.Requires(thn != null);
    Contract.Requires(els == null || els is BlockStmt || els is IfStmt || els is SkeletonStatement);
    this.IsBindingGuard = isBindingGuard;
    this.Guard = guard;
    this.Thn = thn;
    this.Els = els;
  }
  public override IEnumerable<Statement> SubStatements {
    get {
      yield return Thn;
      if (Els != null) {
        yield return Els;
      }
    }
  }
  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      if (Guard != null) {
        yield return Guard;
      }
    }
  }
}