using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class OpaqueBlock : BlockStmt {
  public readonly List<AttributedExpression> Ensures;
  public readonly Specification<FrameExpression> Modifies;

  protected OpaqueBlock(Cloner cloner, OpaqueBlock original) : base(cloner, original) {
    Ensures = original.Ensures.Select(cloner.CloneAttributedExpr).ToList();
    Modifies = cloner.CloneSpecFrameExpr(original.Modifies);
  }

  public OpaqueBlock(RangeToken rangeToken, List<Statement> body, 
    List<AttributedExpression> ensures, 
    Specification<FrameExpression> modifies) : base(rangeToken, body) {
    Ensures = ensures;
    Modifies = modifies;
  }
}