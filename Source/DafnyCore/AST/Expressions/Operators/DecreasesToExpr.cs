using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class DecreasesToExpr : Expression, ICloneable<DecreasesToExpr> {
  public IEnumerable<Expression> OldExpressions { get; }
  public IEnumerable<Expression> NewExpressions { get; }

  public bool AllowNoChange { get; }

  public DecreasesToExpr(IToken tok, IEnumerable<Expression> oldExpressions, IEnumerable<Expression> newExpressions, bool allowNoChange) : base(tok) {
    OldExpressions = oldExpressions;
    NewExpressions = newExpressions;
    AllowNoChange = allowNoChange;
  }

  public DecreasesToExpr(Cloner cloner, DecreasesToExpr original) : base(cloner, original) {
    OldExpressions = original.OldExpressions.Select(cloner.CloneExpr);
    NewExpressions = original.NewExpressions.Select(cloner.CloneExpr);
    // TODO: Type = original.Type if CloneResolvedFields?
  }

  public DecreasesToExpr Clone(Cloner cloner) {
    var result = new DecreasesToExpr(tok,
      OldExpressions.Select(cloner.CloneExpr),
      NewExpressions.Select(cloner.CloneExpr),
      AllowNoChange);
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
}
