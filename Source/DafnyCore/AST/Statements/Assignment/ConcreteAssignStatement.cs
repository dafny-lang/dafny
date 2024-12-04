using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Common superclass of UpdateStmt, AssignSuchThatStmt and AssignOrReturnStmt
/// </summary>
public abstract class ConcreteAssignStatement : Statement, ICanFormat {
  public readonly List<Expression> Lhss;

  protected ConcreteAssignStatement(Cloner cloner, ConcreteAssignStatement original) : base(cloner, original) {
    Lhss = original.Lhss.Select(cloner.CloneExpr).ToList();
  }

  public ConcreteAssignStatement(IOrigin rangeOrigin, List<Expression> lhss, Attributes attrs = null)
    : base(rangeOrigin, attrs) {
    Contract.Requires(cce.NonNullElements(lhss));
    Lhss = lhss;
  }

  public override IEnumerable<INode> Children => Lhss;
  public override IEnumerable<INode> PreResolveChildren => Lhss;
  public override IEnumerable<IdentifierExpr> GetAssignedLocals() {
    return Lhss.Select(lhs => lhs.Resolved).OfType<IdentifierExpr>();
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentUpdateStmt(this, indentBefore, false);
  }

  public virtual void Resolve(ModuleResolver resolver, ResolutionContext context) {
    GenResolve(resolver, context);
  }

  public override void GenResolve(INewOrOldResolver resolver, ResolutionContext context) {
    foreach (var lhs in Lhss) {
      var ec = resolver.Reporter.Count(ErrorLevel.Error);
      resolver.ResolveExpression(lhs, context);
      if (ec == resolver.Reporter.Count(ErrorLevel.Error)) {
        if (lhs is SeqSelectExpr && !((SeqSelectExpr)lhs).SelectOne) {
          resolver.Reporter.Error(MessageSource.Resolver, lhs, "cannot assign to a range of array elements (try the 'forall' statement)");
        }
      }
    }

    base.GenResolve(resolver, context);
  }
}