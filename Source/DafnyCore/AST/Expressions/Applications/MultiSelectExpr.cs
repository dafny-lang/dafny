#nullable enable

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class MultiSelectExpr : Expression, ICloneable<MultiSelectExpr> {
  public Expression Array;
  public List<Expression> Indices;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(1 <= Indices.Count);
  }

  public MultiSelectExpr(Cloner cloner, MultiSelectExpr original) : base(cloner, original) {
    Indices = original.Indices.Select(cloner.CloneExpr).ToList();
    Array = cloner.CloneExpr(original.Array);
  }

  [SyntaxConstructor]
  public MultiSelectExpr(IOrigin origin, Expression array, List<Expression> indices)
    : base(origin) {
    Contract.Requires(1 <= indices.Count);

    Array = array;
    Indices = indices;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Array;
      foreach (var e in Indices) {
        yield return e;
      }
    }
  }

  public MultiSelectExpr Clone(Cloner cloner) {
    return new MultiSelectExpr(cloner, this);
  }
}