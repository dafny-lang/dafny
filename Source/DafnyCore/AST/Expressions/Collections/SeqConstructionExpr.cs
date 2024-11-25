using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class SeqConstructionExpr : Expression, ICloneable<SeqConstructionExpr> {
  public Type/*?*/ ExplicitElementType;
  public Expression N;
  public Expression Initializer;

  public SeqConstructionExpr(Cloner cloner, SeqConstructionExpr original) : base(cloner, original) {
    var elemType = original.ExplicitElementType == null ? null : cloner.CloneType(original.ExplicitElementType);
    N = cloner.CloneExpr(original.N);
    Initializer = cloner.CloneExpr(original.Initializer);
    ExplicitElementType = elemType;
  }

  public SeqConstructionExpr(IOrigin tok, Type/*?*/ elementType, Expression length, Expression initializer)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(length != null);
    Contract.Requires(initializer != null);
    ExplicitElementType = elementType;
    N = length;
    Initializer = initializer;
  }
  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return N;
      yield return Initializer;
    }
  }

  public override IEnumerable<Type> ComponentTypes {
    get {
      if (ExplicitElementType != null) {
        yield return ExplicitElementType;
      }
    }
  }

  public SeqConstructionExpr Clone(Cloner cloner) {
    return new SeqConstructionExpr(cloner, this);
  }
}