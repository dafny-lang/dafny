using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class TypeUnaryExpr : UnaryExpr {
  public Type ToType;

  protected TypeUnaryExpr(Cloner cloner, TypeUnaryExpr original) : base(cloner, original) {
    ToType = cloner.CloneType(original.ToType);
  }

  protected TypeUnaryExpr(IOrigin origin, Expression expr, Type toType)
    : base(origin, expr) {
    Contract.Requires(origin != null);
    Contract.Requires(expr != null);
    Contract.Requires(toType != null);
    ToType = toType;
  }

  public override IEnumerable<INode> Children => base.Children.Concat(ToType.Nodes);

  public override IEnumerable<Type> ComponentTypes {
    get {
      yield return ToType;
    }
  }
}