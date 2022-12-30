using System.Collections.Generic;

namespace Microsoft.Dafny;

public abstract class OneBodyLoopStmt : LoopStmt {
  public readonly BlockStmt/*?*/ Body;
  public WhileStmt.LoopBodySurrogate/*?*/ BodySurrogate;  // set by Resolver; remains null unless Body==null

  public OneBodyLoopStmt(IToken tok, IToken endTok,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt /*?*/ body, Attributes/*?*/ attrs)
    : base(tok, endTok, invariants, decreases, mod, attrs) {
    Body = body;
  }

  public override IEnumerable<Statement> SubStatements {
    get {
      if (Body != null) {
        yield return Body;
      }
    }
  }
}