using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class TypeTestExpr : TypeUnaryExpr, ICloneable<TypeTestExpr> {
  public TypeTestExpr(Cloner cloner, TypeTestExpr original) : base(cloner, original) {
  }

  public TypeTestExpr(IOrigin origin, Expression expr, Type toType)
    : base(origin, expr, toType) {
    Contract.Requires(origin != null);
    Contract.Requires(expr != null);
    Contract.Requires(toType != null);
  }

  public TypeTestExpr Clone(Cloner cloner) {
    return new TypeTestExpr(cloner, this);
  }
}