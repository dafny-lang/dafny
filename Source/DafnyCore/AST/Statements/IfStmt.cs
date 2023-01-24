using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class IfStmt : Statement, ICloneable<IfStmt> {
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

  public IfStmt Clone(Cloner cloner) {
    return new IfStmt(cloner, this);
  }

  public IfStmt(Cloner cloner, IfStmt original) : base(cloner, original) {
    IsBindingGuard = original.IsBindingGuard;
    Guard = cloner.CloneExpr(original.Guard);
    Thn = cloner.CloneBlockStmt(original.Thn);
    Els = cloner.CloneStmt(original.Els);
  }

  public IfStmt(RangeToken rangeToken, bool isBindingGuard, Expression guard, BlockStmt thn, Statement els)
    : base(rangeToken) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
    Contract.Requires(thn != null);
    Contract.Requires(els == null || els is BlockStmt || els is IfStmt || els is SkeletonStatement);
    this.IsBindingGuard = isBindingGuard;
    this.Guard = guard;
    this.Thn = thn;
    this.Els = els;
  }
  public IfStmt(RangeToken rangeToken, bool isBindingGuard, Expression guard, BlockStmt thn, Statement els, Attributes attrs)
    : base(rangeToken, attrs) {
    Contract.Requires(rangeToken != null);
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