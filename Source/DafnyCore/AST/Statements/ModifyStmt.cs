using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ModifyStmt : Statement, ICloneable<ModifyStmt>, ICanFormat {
  public readonly Specification<FrameExpression> Mod;
  public readonly BlockStmt Body;

  public ModifyStmt Clone(Cloner cloner) {
    return new ModifyStmt(cloner, this);
  }

  public ModifyStmt(Cloner cloner, ModifyStmt original) : base(cloner, original) {
    Mod = cloner.CloneSpecFrameExpr(original.Mod);
    Body = cloner.CloneBlockStmt(original.Body);
  }

  public ModifyStmt(RangeToken rangeToken, List<FrameExpression> mod, Attributes attrs, BlockStmt body)
    : base(rangeToken) {
    Contract.Requires(rangeToken != null);
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

  public bool SetIndent(int indentBefore, IndentationFormatter formatter) {
    var commaIndent = indentBefore + formatter.SpaceTab;
    var afterCommaIndent = commaIndent;
    foreach (var token in OwnedTokens) {
      if (formatter.SetIndentLabelTokens(token, indentBefore)) {
        continue;
      }
      switch (token.val) {
        case "modifies":
        case "modify":
          if (IndentationFormatter.IsFollowedByNewline(token)) {
            formatter.SetOpeningIndentedRegion(token, indentBefore);
          } else {
            formatter.SetAlign(indentBefore, token, out afterCommaIndent, out commaIndent);
          }
          break;
        case ",":
          formatter.SetIndentations(token, afterCommaIndent, commaIndent, afterCommaIndent);
          break;
        case "{":
          formatter.SetOpeningIndentedRegion(token, indentBefore);
          break;
        case "}":
        case ";":
          formatter.SetClosingIndentedRegion(token, indentBefore);
          break;
      }
    }

    if (Body != null && Body.StartToken.line > 0) {
      formatter.SetOpeningIndentedRegion(Body.StartToken, indentBefore);
    }

    return true;
  }
}