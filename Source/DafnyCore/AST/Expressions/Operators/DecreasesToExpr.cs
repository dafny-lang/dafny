using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class DecreasesToExpr : Expression, ICloneable<DecreasesToExpr>, ICanFormat {
  public IEnumerable<Expression> OldExpressions { get; }
  public IEnumerable<Expression> NewExpressions { get; }

  public DecreasesToExpr(IToken tok, IEnumerable<Expression> oldExpressions, IEnumerable<Expression> newExpressions) : base(tok) {
    OldExpressions = oldExpressions;
    NewExpressions = newExpressions;
  }

  public DecreasesToExpr(Cloner cloner, DecreasesToExpr original) : base(cloner, original) {
    OldExpressions = original.OldExpressions.Select(cloner.CloneExpr);
    NewExpressions = original.NewExpressions.Select(cloner.CloneExpr);
    // TODO: Type = original.Type if CloneResolvedFields?
  }

  public DecreasesToExpr Clone(Cloner cloner) {
    var result = new DecreasesToExpr(tok,
      OldExpressions.Select(cloner.CloneExpr),
      NewExpressions.Select(cloner.CloneExpr));
    if (cloner.CloneResolvedFields) {
      result.Type = Type;
    }
    return result;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      foreach (var oldExpr in OldExpressions) {
        yield return oldExpr;
      }
      foreach (var newExpr in NewExpressions) {
        yield return newExpr;
      }
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    throw new NotImplementedException();
  }
}
