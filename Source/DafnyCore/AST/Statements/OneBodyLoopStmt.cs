using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny.Auditor;

namespace Microsoft.Dafny;

public abstract class OneBodyLoopStmt : LoopStmt {
  public readonly BlockStmt/*?*/ Body;
  [FilledInDuringResolution]
  public WhileStmt.LoopBodySurrogate/*?*/ BodySurrogate;  // set by Resolver; remains null unless Body==null

  protected OneBodyLoopStmt(Cloner cloner, OneBodyLoopStmt original) : base(cloner, original) {
    Body = (BlockStmt)cloner.CloneStmt(original.Body);
    if (cloner.CloneResolvedFields) {
      if (original.BodySurrogate != null) {
        BodySurrogate = new WhileStmt.LoopBodySurrogate(
          original.BodySurrogate.LocalLoopTargets.Select(v => cloner.CloneIVariable(v, true)).ToList(),
          original.BodySurrogate.UsesHeap);
      }
    }
  }

  protected OneBodyLoopStmt(RangeToken rangeToken,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt /*?*/ body, Attributes/*?*/ attrs)
    : base(rangeToken, invariants, decreases, mod, attrs) {
    Body = body;
  }

  public override IEnumerable<Statement> SubStatements {
    get {
      if (Body != null) {
        yield return Body;
      }
    }
  }

  public override IEnumerable<Assumption> Assumptions() {
    if (Body is null) {
      yield return new Assumption(tok, AssumptionDescription.LoopWithoutBody);
    }
  }
}