#nullable enable

using System.Collections.Generic;

namespace Microsoft.Dafny;

public class SeqDisplayExpr : DisplayExpression, ICanFormat, ICloneable<SeqDisplayExpr> {
  [SyntaxConstructor]
  public SeqDisplayExpr(IOrigin origin, List<Expression> elements) : base(origin, elements) { }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentParensExpression(indentBefore, OwnedTokens);
  }

  public SeqDisplayExpr(Cloner cloner, SeqDisplayExpr original) : base(cloner, original) {
  }

  public SeqDisplayExpr Clone(Cloner cloner) {
    return new SeqDisplayExpr(cloner, this);
  }
}