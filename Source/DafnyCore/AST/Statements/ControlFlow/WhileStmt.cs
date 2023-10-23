using System.Collections.Generic;

namespace Microsoft.Dafny;

public class WhileStmt : OneBodyLoopStmt, ICloneable<WhileStmt>, ICanFormat {
  public readonly Expression/*?*/ Guard;

  public class LoopBodySurrogate {
    public readonly List<IVariable> LocalLoopTargets;
    public readonly bool UsesHeap;

    public LoopBodySurrogate(List<IVariable> localLoopTargets, bool usesHeap) {
      LocalLoopTargets = localLoopTargets;
      UsesHeap = usesHeap;
    }
  }

  public WhileStmt Clone(Cloner cloner) {
    return new WhileStmt(cloner, this);
  }

  public WhileStmt(Cloner cloner, WhileStmt original) : base(cloner, original) {
    Guard = cloner.CloneExpr(original.Guard);
  }

  public WhileStmt(RangeToken rangeToken, Expression guard,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt body)
    : base(rangeToken, invariants, decreases, mod, body, null) {
    this.Guard = guard;
  }

  public WhileStmt(RangeToken rangeToken, Expression guard,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt body, Attributes attrs)
    : base(rangeToken, invariants, decreases, mod, body, attrs) {
    this.Guard = guard;
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      if (Guard != null) {
        yield return Guard;
      }
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    formatter.SetIndentLikeLoop(OwnedTokens, Body, indentBefore);
    foreach (var ens in Invariants) {
      formatter.SetAttributedExpressionIndentation(ens, indentBefore + formatter.SpaceTab);
    }

    foreach (var dec in Decreases.Expressions) {
      formatter.SetDecreasesExpressionIndentation(dec, indentBefore + formatter.SpaceTab);
    }

    if (EndToken.val == "}") {
      formatter.SetClosingIndentedRegion(EndToken, indentBefore);
    }

    return false;
  }
}