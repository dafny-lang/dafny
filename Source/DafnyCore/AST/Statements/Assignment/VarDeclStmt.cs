using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class VarDeclStmt : Statement, ICloneable<VarDeclStmt>, ICanFormat {
  public readonly List<LocalVariable> Locals;
  public readonly ConcreteUpdateStatement Update;
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
    Update = (ConcreteUpdateStatement)cloner.CloneStmt(original.Update);
  }

  public VarDeclStmt(RangeToken rangeToken, List<LocalVariable> locals, ConcreteUpdateStatement update)
    : base(rangeToken) {
    Contract.Requires(locals != null);
    Contract.Requires(locals.Count != 0);

    Locals = locals;
    Update = update;
  }

  public override IEnumerable<Statement> SubStatements {
    get { if (Update != null) { yield return Update; } }
  }

  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      foreach (var v in Locals) {
        foreach (var e in Attributes.SubExpressions(v.Attributes)) {
          yield return e;
        }
      }

      if (this.Update != null) {
        foreach (var e in this.Update.NonSpecificationSubExpressions) {
          yield return e;
        }
      }
    }
  }

  public override IEnumerable<Node> Children => Locals.Concat<Node>(SubStatements);

  public override IEnumerable<Node> PreResolveChildren => Children;
  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var result = formatter.SetIndentVarDeclStmt(indentBefore, OwnedTokens, false, false);
    return Update != null ? formatter.SetIndentUpdateStmt(Update, indentBefore, true) : result;
  }
}