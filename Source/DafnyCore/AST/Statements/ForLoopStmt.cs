using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ForLoopStmt : OneBodyLoopStmt, ICloneable<ForLoopStmt> {
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

  public ForLoopStmt(IToken tok, IToken endTok, BoundVar loopIndexVariable, Expression start, Expression/*?*/ end, bool goingUp,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt /*?*/ body, Attributes attrs)
    : base(tok, endTok, invariants, decreases, mod, body, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
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
}
