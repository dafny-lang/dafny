using Microsoft.BaseTypes;

namespace Microsoft.Dafny;

public static class FloatLiteralValidator {
  public static (bool isExact, BigFloat floatValue) ValidateAndCompute(
    BigDec decValue, int significandBits, int exponentBits) {
    var isExact = BigFloat.FromBigDec(decValue, significandBits, exponentBits, out var floatValue);
    return (isExact, floatValue);
  }

  public static BigFloat ComputeNegatedFloat(BigDec decValue, int significandBits, int exponentBits) {
    if (decValue.IsZero) {
      return BigFloat.CreateZero(true, significandBits, exponentBits);
    }
    BigFloat.FromBigDec(-decValue, significandBits, exponentBits, out var negatedFloat);
    return negatedFloat;
  }
}
