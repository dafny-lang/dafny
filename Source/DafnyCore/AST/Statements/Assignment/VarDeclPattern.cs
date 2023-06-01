using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class VarDeclPattern : Statement, ICloneable<VarDeclPattern>, ICanFormat {
  public readonly CasePattern<LocalVariable> LHS;
  public readonly Expression RHS;
  public bool HasGhostModifier;

  public VarDeclPattern Clone(Cloner cloner) {
    return new VarDeclPattern(cloner, this);
  }

  public VarDeclPattern(Cloner cloner, VarDeclPattern original) : base(cloner, original) {
    LHS = cloner.CloneCasePattern(original.LHS);
    RHS = cloner.CloneExpr(original.RHS);
    HasGhostModifier = original.HasGhostModifier;
  }

  public VarDeclPattern(RangeToken rangeToken, CasePattern<LocalVariable> lhs, Expression rhs, bool hasGhostModifier)
    : base(rangeToken) {
    LHS = lhs;
    RHS = rhs;
    HasGhostModifier = hasGhostModifier;
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) {
        yield return e;
      }
      yield return RHS;
    }
  }

  public override IEnumerable<Node> Children =>
    new List<Node> { LHS }.Concat(base.Children);

  public IEnumerable<LocalVariable> LocalVars {
    get {
      foreach (var bv in LHS.Vars) {
        yield return bv;
      }
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentVarDeclStmt(indentBefore, OwnedTokens, false, true);
  }
}