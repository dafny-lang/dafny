using System.Collections.Generic;

namespace Microsoft.Dafny;

public class ApplyExpr : Expression, ICloneable<ApplyExpr> {
  // The idea is that this apply expression does not need a type argument substitution,
  // since lambda functions and anonymous functions are never polymorphic.
  // Make a FunctionCallExpr otherwise, to call a resolvable anonymous function.
  public Expression Function;
  public List<Expression> Args;

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Function;
      foreach (var e in Args) {
        yield return e;
      }
    }
  }

  public Token CloseParen;

  public ApplyExpr(Cloner cloner, ApplyExpr original) : base(cloner, original) {
    Function = cloner.CloneExpr(original.Function);
    Args = original.Args.ConvertAll(cloner.CloneExpr);
    CloseParen = original.CloseParen;
  }

  public ApplyExpr(IOrigin origin, Expression fn, List<Expression> args, Token closeParen)
    : base(origin) {
    Function = fn;
    Args = args;
    CloseParen = closeParen;
  }

  public ApplyExpr Clone(Cloner cloner) {
    return new ApplyExpr(cloner, this);
  }
}