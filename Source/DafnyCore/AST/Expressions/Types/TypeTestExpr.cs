using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class TypeTestExpr : TypeUnaryExpr, ICloneable<TypeTestExpr> {
  public TypeTestExpr(Cloner cloner, TypeTestExpr original) : base(cloner, original) {
  }

  public TypeTestExpr(IOrigin tok, Expression expr, Type toType)
    : base(tok, expr, toType) {
    Contract.Requires(tok != null);
    Contract.Requires(expr != null);
    Contract.Requires(toType != null);
  }

  public TypeTestExpr Clone(Cloner cloner) {
    return new TypeTestExpr(cloner, this);
  }
}