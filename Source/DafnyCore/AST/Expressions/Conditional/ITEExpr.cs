using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ITEExpr : Expression, ICanFormat, ICloneable<ITEExpr> {
  public bool IsBindingGuard;
  public Expression Test;
  public Expression Thn;
  public Expression Els;

  public ITEExpr(Cloner cloner, ITEExpr original) : base(cloner, original) {
    IsBindingGuard = original.IsBindingGuard;
    Test = cloner.CloneExpr(original.Test);
    Thn = cloner.CloneExpr(original.Thn);
    Els = cloner.CloneExpr(original.Els);
  }

  public enum ITECompilation {
    CompileBothBranches,
    CompileJustThenBranch,
    CompileJustElseBranch
  };
  public ITECompilation HowToCompile = ITECompilation.CompileBothBranches; // updated by CheckIsCompilable during resolution

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Test != null);
    Contract.Invariant(Thn != null);
    Contract.Invariant(Els != null);
  }

  [SyntaxConstructor]
  public ITEExpr(IOrigin origin, bool isBindingGuard, Expression test, Expression thn, Expression els)
    : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(test != null);
    Contract.Requires(thn != null);
    Contract.Requires(els != null);
    this.IsBindingGuard = isBindingGuard;
    this.Test = test;
    this.Thn = thn;
    this.Els = els;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Test;
      yield return Thn;
      yield return Els;
    }
  }

  public override IEnumerable<Expression> TerminalExpressions {
    get {
      foreach (var e in Thn.TerminalExpressions) {
        yield return e;
      }
      foreach (var e in Els.TerminalExpressions) {
        yield return e;
      }
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var lineThen = 0;
    var colThen = 0;
    Token thenToken = null;
    foreach (var token in OwnedTokens) {
      switch (token.val) {
        case "if": {
            if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
              formatter.SetOpeningIndentedRegion(token, indentBefore);
            } else {
              formatter.SetAlignOpen(token, indentBefore);
            }
            formatter.Visit(Test, indentBefore);
            break;
          }
        case "then": {
            lineThen = token.line;
            colThen = token.col;
            thenToken = token;
            if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
              formatter.SetOpeningIndentedRegion(token, indentBefore);
            } else {
              var rightIndent = formatter.GetRightAlignIndentAfter(token, indentBefore);
              formatter.SetIndentations(token, indentBefore, indentBefore, rightIndent);
            }
            formatter.Visit(Thn, indentBefore + formatter.SpaceTab);            // Override the last indentation so that comments are on the same column as "else"
            formatter.SetIndentations(token.Prev, below: indentBefore);

            break;
          }
        case "else": {
            if (token.col == colThen) {
              // We keep the alignment.
              var newElseIndent = formatter.GetNewTokenVisualIndent(thenToken, indentBefore);
              formatter.SetDelimiterIndentedRegions(token, newElseIndent);
            } else if (token.Next.val == "if" || token.line == lineThen) { // Don't indent the subexpression
              formatter.SetIndentations(token, above: indentBefore, inline: indentBefore, below: indentBefore);
            } else if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
              formatter.SetOpeningIndentedRegion(token, indentBefore);
            } else {
              formatter.SetAlign(indentBefore, token, out _, out _);
            }

            formatter.Visit(Els, indentBefore + formatter.SpaceTab);
            // Override the last indentation so that comments are on the same column as "else"
            formatter.SetIndentations(token.Prev, below: indentBefore);
            break;
          }
      }
    }

    return false;
  }

  public ITEExpr Clone(Cloner cloner) {
    return new ITEExpr(cloner, this);
  }
}