using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class AutoGeneratedOrigin : OriginWrapper {
  
  public AutoGeneratedOrigin(IOrigin wrappedToken)
    : base(wrappedToken) {
    Contract.Requires(wrappedToken != null);
  }

  public static IOrigin Unwrap(IOrigin token) {
    if (token is AutoGeneratedOrigin autoGeneratedToken) {
      return Unwrap(autoGeneratedToken.WrappedToken);
    }

    return token;
  }

  public static bool Is(IOrigin tok) {
    while (tok is OriginWrapper w) {
      if (w is AutoGeneratedOrigin) {
        return true;
      }
      tok = w.WrappedToken;
    }
    return false;
  }

  public static Expression WrapExpression(Expression expr) {
    return Expression.CreateParensExpression(new AutoGeneratedOrigin(expr.Origin), expr);
  }

  public override IOrigin WithVal(string newVal) {
    return new AutoGeneratedOrigin(WrappedToken.WithVal(newVal));
  }

  public override bool IsCopy => true;
}