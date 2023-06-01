using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ForLoopStmt : OneBodyLoopStmt, ICloneable<ForLoopStmt>, ICanFormat {
  public readonly BoundVar LoopIndex;
  public readonly Expression Start;
  public readonly Expression/*?*/ End;
  public readonly bool GoingUp;

  public ForLoopStmt Clone(Cloner cloner) {
    return new ForLoopStmt(cloner, this);
  }

  public ForLoopStmt(Cloner cloner, ForLoopStmt original) : base(cloner, original) {
    LoopIndex = cloner.CloneBoundVar(original.LoopIndex, false);
    Start = cloner.CloneExpr(original.Start);
    End = cloner.CloneExpr(original.End);
    GoingUp = original.GoingUp;
  }

  public ForLoopStmt(RangeToken rangeToken, BoundVar loopIndexVariable, Expression start, Expression/*?*/ end, bool goingUp,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt /*?*/ body, Attributes attrs)
    : base(rangeToken, invariants, decreases, mod, body, attrs) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(loopIndexVariable != null);
    Contract.Requires(start != null);
    Contract.Requires(invariants != null);
    Contract.Requires(decreases != null);
    Contract.Requires(mod != null);
    LoopIndex = loopIndexVariable;
    Start = start;
    End = end;
    GoingUp = goingUp;
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      yield return Start;
      if (End != null) {
        yield return End;
      }
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var forReached = false;
    var specification = false;
    foreach (var token in OwnedTokens) {
      if (formatter.SetIndentLabelTokens(token, indentBefore)) {
        continue;
      }
      if (token.val == "for") {
        formatter.SetOpeningIndentedRegion(token, indentBefore);
        forReached = true;
        continue;
      }

      if (!forReached) {
        continue;
      }

      if (specification) {
        formatter.SetOpeningIndentedRegion(token, indentBefore + formatter.SpaceTab);
      }

      if (token.val is "to" or "downto") {
        specification = true;
      }
    }

    foreach (var ens in Invariants) {
      formatter.SetAttributedExpressionIndentation(ens, indentBefore + formatter.SpaceTab);
    }

    formatter.SetIndentBody(Body, indentBefore);
    formatter.SetClosingIndentedRegion(EndToken, indentBefore);
    return false;
  }
}
