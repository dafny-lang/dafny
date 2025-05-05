using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class TypeTestExpr : TypeUnaryExpr, ICloneable<TypeTestExpr> {
  public TypeTestExpr(Cloner cloner, TypeTestExpr original) : base(cloner, original) {
  }

  [SyntaxConstructor]
  public TypeTestExpr(IOrigin origin, Expression e, Type toType)
    : base(origin, e, toType) {
    Contract.Requires(origin != null);
    Contract.Requires(e != null);
    Contract.Requires(toType != null);
  }

  public TypeTestExpr Clone(Cloner cloner) {
    return new TypeTestExpr(cloner, this);
  }
}