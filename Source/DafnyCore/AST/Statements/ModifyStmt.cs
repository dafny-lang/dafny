using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ModifyStmt : Statement {
  public readonly Specification<FrameExpression> Mod;
  public readonly BlockStmt Body;

  public ModifyStmt(IToken tok, IToken endTok, List<FrameExpression> mod, Attributes attrs, BlockStmt body)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(mod != null);
    Mod = new Specification<FrameExpression>(mod, attrs);
    Body = body;
  }

  public override IEnumerable<Statement> SubStatements {
    get {
      if (Body != null) {
        yield return Body;
      }
    }
  }
  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      foreach (var e in Attributes.SubExpressions(Mod.Attributes)) { yield return e; }
      foreach (var fe in Mod.Expressions) {
        yield return fe.E;
      }
    }
  }
}