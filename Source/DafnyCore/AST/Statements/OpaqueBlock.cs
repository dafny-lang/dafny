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

  public override void GenResolve(INewOrOldResolver resolver, ResolutionContext resolutionContext) {

    resolver.Scope.PushMarker();
    foreach (Statement ss in Body) {
      resolver.ResolveStatementWithLabels(ss, resolutionContext);
    }
    resolver.Scope.PopMarker();

    resolver.ResolveAttributes(Modifies, resolutionContext);
    foreach (var fe in Modifies.Expressions) {
      resolver.ResolveFrameExpression(fe, FrameExpressionUse.Modifies, resolutionContext);
    }

    foreach (var e in Ensures) {
      resolver.ResolveAttributes(e, resolutionContext);
      resolver.ResolveExpression(e.E, resolutionContext);
      resolver.ConstrainTypeExprBool(e.E, "Postcondition must be a boolean (got {0})");
    }
    base.GenResolve(resolver, resolutionContext);
  }
}