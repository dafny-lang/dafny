using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class LambdaExpr : ComprehensionExpr, ICloneable<LambdaExpr>, ICanFormat {
  public override string WhatKind => "lambda";

  public Expression Body => Term;

  public readonly List<FrameExpression> Reads;

  public LambdaExpr(IToken tok, RangeToken rangeToken, List<BoundVar> bvars, Expression requires, List<FrameExpression> reads, Expression body)
    : base(tok, rangeToken, bvars, requires, body, null) {
    Contract.Requires(reads != null);
    Reads = reads;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Term;
      if (Range != null) {
        yield return Range;
      }
      foreach (var read in Reads) {
        yield return read.E;
      }
    }
  }

  public LambdaExpr(Cloner cloner, LambdaExpr original) : base(cloner, original) {
    Reads = original.Reads.ConvertAll(cloner.CloneFrameExpr);
  }

  public LambdaExpr Clone(Cloner cloner) {
    return new LambdaExpr(cloner, this);
  }

  public override bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var itemIndent = indentBefore + formatter.SpaceTab;
    var commaIndent = indentBefore;
    var firstSpec = true;
    var specIndent = indentBefore + formatter.SpaceTab;
    foreach (var token in OwnedTokens) {
      switch (token.val) {
        case "(": {
            if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
              formatter.SetIndentations(token, indentBefore, indentBefore, itemIndent);
            } else {
              formatter.SetAlign(indentBefore, token, out itemIndent, out commaIndent);
            }

            break;
          }
        case ")": {
            formatter.SetIndentations(token, itemIndent, indentBefore, indentBefore);
            break;
          }
        case ",": {
            formatter.SetIndentations(token, itemIndent, commaIndent, itemIndent);
            break;
          }
        case "requires":
        case "reads": {
            if (firstSpec) {
              specIndent = formatter.GetNewTokenVisualIndent(token, indentBefore);
              firstSpec = false;
            }
            formatter.SetIndentations(token, specIndent, specIndent, specIndent + formatter.SpaceTab);
            break;
          }
        case "=>": {
            formatter.SetIndentations(token, itemIndent, indentBefore, indentBefore + formatter.SpaceTab);
            break;
          }
      }
    }

    foreach (var bv in BoundVars) {
      if (bv.SyntacticType != null) {
        formatter.SetTypeIndentation(bv.SyntacticType);
      }
    }

    return true;
  }
}