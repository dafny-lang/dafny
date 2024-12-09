using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class SeqDisplayExpr : DisplayExpression, ICanFormat, ICloneable<SeqDisplayExpr> {
  public SeqDisplayExpr(IOrigin tok, List<Expression> elements)
    : base(tok, elements) {
    Contract.Requires(cce.NonNullElements(elements));
    Contract.Requires(tok != null);
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentParensExpression(indentBefore, OwnedTokens);
  }

  public SeqDisplayExpr(Cloner cloner, SeqDisplayExpr original) : base(cloner, original) {
  }

  public SeqDisplayExpr Clone(Cloner cloner) {
    return new SeqDisplayExpr(cloner, this);
  }
}