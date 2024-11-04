using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class VarDeclStmt : Statement, ICloneable<VarDeclStmt>, ICanFormat {
  public readonly List<LocalVariable> Locals;
  public readonly ConcreteAssignStatement Assign;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Locals));
    Contract.Invariant(Locals.Count != 0);
  }

  public VarDeclStmt Clone(Cloner cloner) {
    return new VarDeclStmt(cloner, this);
  }

  public VarDeclStmt(Cloner cloner, VarDeclStmt original) : base(cloner, original) {
    Locals = original.Locals.Select(l => cloner.CloneLocalVariable(l, false)).ToList();
    Assign = (ConcreteAssignStatement)cloner.CloneStmt(original.Assign, false);
  }

  public VarDeclStmt(RangeToken rangeToken, List<LocalVariable> locals, ConcreteAssignStatement assign)
    : base(rangeToken) {
    Contract.Requires(locals != null);
    Contract.Requires(locals.Count != 0);

    Locals = locals;
    Assign = assign;
  }

  public override IEnumerable<Statement> SubStatements {
    get { if (Assign != null) { yield return Assign; } }
  }

  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      foreach (var v in Locals) {
        foreach (var e in Attributes.SubExpressions(v.Attributes)) {
          yield return e;
        }
      }
    }
  }

  public override IEnumerable<INode> Children => Locals.Concat<Node>(SubStatements);

  public override IEnumerable<INode> PreResolveChildren => Children;
  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var result = formatter.SetIndentVarDeclStmt(indentBefore, OwnedTokens, false, false);
    return Assign != null ? formatter.SetIndentUpdateStmt(Assign, indentBefore, true) : result;
  }
}