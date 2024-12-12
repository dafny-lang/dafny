using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class SeqSelectExpr : Expression, ICloneable<SeqSelectExpr> {
  public readonly bool SelectOne;  // false means select a range
  public readonly Expression Seq;
  public readonly Expression E0;
  public readonly Expression E1;
  public readonly Token CloseParen;

  public SeqSelectExpr(Cloner cloner, SeqSelectExpr original) : base(cloner, original) {
    SelectOne = original.SelectOne;
    Seq = cloner.CloneExpr(original.Seq);
    E0 = cloner.CloneExpr(original.E0);
    E1 = cloner.CloneExpr(original.E1);
    CloseParen = original.CloseParen;
  }

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Seq != null);
    Contract.Invariant(!SelectOne || E1 == null);
  }

  public SeqSelectExpr(IOrigin tok, bool selectOne, Expression seq, Expression e0, Expression e1, Token closeParen)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(seq != null);
    Contract.Requires(!selectOne || e1 == null);

    SelectOne = selectOne;
    Seq = seq;
    E0 = e0;
    E1 = e1;
    CloseParen = closeParen;
    if (closeParen != null) {
      FormatTokens = new[] { closeParen };
    }
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Seq;
      if (E0 != null) {
        yield return E0;
      }

      if (E1 != null) {
        yield return E1;
      }
    }
  }

  public SeqSelectExpr Clone(Cloner cloner) {
    return new SeqSelectExpr(cloner, this);
  }
}