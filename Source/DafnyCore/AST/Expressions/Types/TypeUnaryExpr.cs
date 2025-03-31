#nullable enable

using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class TypeUnaryExpr : UnaryExpr {
  public Type ToType;

  protected TypeUnaryExpr(Cloner cloner, TypeUnaryExpr original) : base(cloner, original) {
    ToType = cloner.CloneType(original.ToType);
  }

  [SyntaxConstructor]
  protected TypeUnaryExpr(IOrigin origin, Expression e, Type toType)
    : base(origin, e) {
    ToType = toType;
  }

  public override IEnumerable<INode> Children => base.Children.Concat(ToType.Nodes);

  public override IEnumerable<Type> ComponentTypes {
    get {
      yield return ToType;
    }
  }
}