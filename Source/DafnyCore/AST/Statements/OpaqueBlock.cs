#nullable enable
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class OpaqueBlock : BlockStmt, ICanResolveNewAndOld, ICloneable<OpaqueBlock> {
  public List<AttributedExpression> Ensures;

  /**
   * Default is empty. Does not assume the method modifies as a default
   */
  public Specification<FrameExpression> Modifies;

  protected OpaqueBlock(Cloner cloner, OpaqueBlock original) : base(cloner, original) {
    Ensures = original.Ensures.Select(cloner.CloneAttributedExpr).ToList();
    Modifies = cloner.CloneSpecFrameExpr(original.Modifies);
  }

  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in Ensures) {
        yield return e.E;
      }
      foreach (var e in Modifies.Expressions!) {
        yield return e.E;
      }
    }
  }

  [SyntaxConstructor]
  public OpaqueBlock(IOrigin origin, List<Statement> body,
    List<AttributedExpression> ensures,
    Specification<FrameExpression> modifies, List<Label> labels, Attributes? attributes = null)
    : base(origin, body, labels, attributes) {
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
    foreach (var fe in Modifies.Expressions!) {
      resolver.ResolveFrameExpression(fe, FrameExpressionUse.Modifies, resolutionContext);
    }

    foreach (var ensure in Ensures) {
      resolver.ResolveAttributes(ensure, resolutionContext);
      resolver.ResolveExpression(ensure.E, resolutionContext);
      resolver.ConstrainTypeExprBool(ensure.E, "Postcondition must be a boolean (got {0})");
    }
    base.GenResolve(resolver, resolutionContext);
  }

  public new OpaqueBlock Clone(Cloner cloner) {
    return new OpaqueBlock(cloner, this);
  }
}