// This file is translated by hand.  References to it are rewritten using the
// --rewrite flag (to respect's Dafny's module structure).

namespace App.ExactArithmetic {
  public struct Decimal {
    int Mantissa;
    int Exponent;

    public Decimal(int mantissa, int exponent) {
      Mantissa = mantissa;
      Exponent = exponent;
    }

    public string ToStr() => String.Intern($"{Mantissa * Math.Pow(10, Exponent):0.00}");
  }
}
