#nullable enable

using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class LambdaExpr : ComprehensionExpr, ICloneable<LambdaExpr>, IFrameScope {
  public override string WhatKind => Reads.Expressions is { Count: > 0 } ? "lambda" : Range != null ? "partial lambda" : "total lambda";

  public Expression Body => Term;

  public Specification<FrameExpression> Reads;

  [SyntaxConstructor]
  public LambdaExpr(IOrigin origin, List<BoundVar> boundVars, Expression? range, Specification<FrameExpression> reads, Expression term, Attributes? attributes = null)
    : base(origin, boundVars, range, term, attributes) {
    Reads = reads;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Term;
      if (Range != null) {
        yield return Range;
      }
      if (Reads.Expressions == null) {
        yield break;
      }
      foreach (var read in Reads.Expressions) {
        yield return read.E;
      }
    }
  }

  public LambdaExpr(Cloner cloner, LambdaExpr original) : base(cloner, original) {
    Reads = cloner.CloneSpecFrameExpr(original.Reads);
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
      if (bv.IsTypeExplicit) {
        formatter.SetTypeIndentation(bv.SyntacticType);
      }
    }

    return true;
  }

  public string Designator => "lambda";
}