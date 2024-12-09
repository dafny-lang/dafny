using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class DecreasesToExpr : Expression, ICloneable<DecreasesToExpr> {
  public IReadOnlyList<Expression> OldExpressions { get; }
  public IReadOnlyList<Expression> NewExpressions { get; }

  public bool AllowNoChange { get; }

  public DecreasesToExpr(IOrigin tok,
    IReadOnlyList<Expression> oldExpressions,
    IReadOnlyList<Expression> newExpressions, bool allowNoChange) : base(tok) {
    OldExpressions = oldExpressions;
    NewExpressions = newExpressions;
    AllowNoChange = allowNoChange;
  }

  public DecreasesToExpr(Cloner cloner, DecreasesToExpr original) : base(cloner, original) {
    OldExpressions = original.OldExpressions.Select(cloner.CloneExpr).ToList();
    NewExpressions = original.NewExpressions.Select(cloner.CloneExpr).ToList();
    AllowNoChange = original.AllowNoChange;
  }

  public DecreasesToExpr Clone(Cloner cloner) {
    return new DecreasesToExpr(cloner, this);
  }

  public override IEnumerable<Expression> SubExpressions => OldExpressions.Concat(NewExpressions);
}
