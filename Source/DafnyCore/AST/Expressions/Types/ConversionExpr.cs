using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ConversionExpr : TypeUnaryExpr, ICloneable<ConversionExpr> {
  public readonly string messagePrefix;

  public ConversionExpr(Cloner cloner, ConversionExpr original) : base(cloner, original) {
    messagePrefix = original.messagePrefix;
  }

  public ConversionExpr(IOrigin tok, Expression expr, Type toType, string messagePrefix = "")
    : base(tok, expr, toType) {
    Contract.Requires(tok != null);
    Contract.Requires(expr != null);
    Contract.Requires(toType != null);
    this.messagePrefix = messagePrefix;
  }

  public ConversionExpr Clone(Cloner cloner) {
    return new ConversionExpr(cloner, this);
  }
}