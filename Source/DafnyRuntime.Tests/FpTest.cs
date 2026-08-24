using System;
using System.Collections.Generic;
using System.Numerics;
using Dafny;
using Xunit;

namespace DafnyRuntime.Tests;

/// <summary>
/// Dafny.Fp32/Fp64 exist so that compiled floating point agrees with what the verifier proved.
/// The verifier's "==" is value identity in the SMT FloatingPoint sort -- every NaN is one value,
/// and -0.0 and +0.0 are two -- while C#'s "==" on double is IEEE fp.eq, which disagrees on
/// exactly those points. These tests pin down that the wrappers implement the verifier's
/// semantics and that IEEE remains reachable under its own names.
/// </summary>
public class FpTest {
  private static readonly Fp64 PosZero = new Fp64(0.0);
  private static readonly Fp64 NegZero = new Fp64(-0.0);
  private static readonly Fp64 NaN = new Fp64(double.NaN);
  // A NaN with a non-default payload, and one with the sign bit set. The SMT FloatingPoint sort
  // has a single NaN, so Dafny must not be able to tell any of the three apart.
  private static readonly Fp64 NaNPayload = Fp64.FromDoubleBits(unchecked((long)0x7ff8000000000123UL));
  private static readonly Fp64 NegNaN = Fp64.FromDoubleBits(unchecked((long)0xfff8000000000000UL));

  [Fact]
  public void EqualityIsValueIdentityNotIeee() {
    Assert.False(PosZero == NegZero);
    Assert.True(NaN == NaN);
    Assert.True(NaN == NaNPayload);
    Assert.True(NaN == NegNaN);
  }

  [Fact]
  public void EqualObjectsHaveEqualHashCodes() {
    Assert.Equal(NaN.GetHashCode(), NaNPayload.GetHashCode());
    Assert.Equal(NaN.GetHashCode(), NegNaN.GetHashCode());
    Assert.NotEqual(PosZero.GetHashCode(), NegZero.GetHashCode());
  }

  [Fact]
  public void IeeeEqualityStillAvailableForFpEqual() {
    // fp64.Equal(x, y) in Dafny is IEEE fp.eq and must keep disagreeing with "==".
    Assert.True(Fp64.IeeeEqual(PosZero, NegZero));
    Assert.False(Fp64.IeeeEqual(NaN, NaN));
  }

  [Fact]
  public void OrderPutsNegativeZeroBelowPositiveZero() {
    // Dafny refines fp.lt so that "<" agrees with "==": since -0.0 != +0.0, one is below the other.
    Assert.True(NegZero < PosZero);
    Assert.False(PosZero < NegZero);
    Assert.True(NegZero <= PosZero);
    Assert.False(PosZero <= NegZero);
    // Antisymmetry, which raw fp.leq breaks at zero.
    Assert.False(NegZero <= PosZero && PosZero <= NegZero);
    // fp64.Less is the unrefined IEEE predicate.
    Assert.False(Fp64.IeeeLess(NegZero, PosZero));
  }

  [Fact]
  public void NaNIsOutsideTheOrder() {
    var one = new Fp64(1.0);
    Assert.False(one < NaN);
    Assert.False(NaN < one);
    Assert.False(one <= NaN);
    Assert.False(NaN <= one);
  }

  [Fact]
  public void HashAndComparisonCollectionsAgree() {
    var values = new[] { PosZero, NegZero, NaN, NaNPayload, NegNaN };
    // Three distinct Dafny values: -0.0, +0.0, NaN.
    Assert.Equal(3, new HashSet<Fp64>(values).Count);
    var sorted = new SortedSet<Fp64>(values, Fp64.DafnyOrderComparer.Instance);
    Assert.Equal(3, sorted.Count);
  }

  [Fact]
  public void ComparerAgreesWithEquality() {
    // A SortedSet is only consistent with Equals if Compare returns 0 exactly when Equals holds.
    var values = new[] {
      PosZero, NegZero, NaN, NaNPayload, NegNaN, new Fp64(1.0), new Fp64(-1.0),
      new Fp64(double.PositiveInfinity), new Fp64(double.NegativeInfinity),
      new Fp64(double.Epsilon), new Fp64(-double.Epsilon),
      new Fp64(double.MaxValue), new Fp64(double.MinValue)
    };
    foreach (var a in values) {
      foreach (var b in values) {
        var compared = Fp64.DafnyOrderComparer.Instance.Compare(a, b);
        Assert.Equal(a == b, compared == 0);
        // Where Dafny orders the pair, the comparer must not contradict it.
        if (a < b) {
          Assert.True(compared < 0);
        }
      }
    }
  }

  [Fact]
  public void DictionaryKeysDistinguishTheTwoZeros() {
    var d = new Dictionary<Fp64, int> { [PosZero] = 1, [NegZero] = 2 };
    Assert.Equal(2, d.Count);
    Assert.Equal(1, d[PosZero]);
    Assert.Equal(2, d[NegZero]);
  }

  [Theory]
  [InlineData(1.5, "1.5")]
  [InlineData(0.0, "0.0")]
  [InlineData(-0.0, "-0.0")]
  [InlineData(2.0, "2.0")]
  [InlineData(0.1, "0.1")]
  [InlineData(double.NaN, "NaN")]
  [InlineData(double.PositiveInfinity, "Infinity")]
  [InlineData(double.NegativeInfinity, "-Infinity")]
  public void ToStringKeepsTheSignAndTheDecimalPoint(double value, string expected) {
    Assert.Equal(expected, new Fp64(value).ToString());
  }

  [Theory]
  // Extreme values print in scientific form, written the way a Dafny literal is written -- a
  // lowercase marker and no "+" -- so that printed output can be read back as source.
  [InlineData(double.MaxValue, "1.7976931348623157e308")]
  [InlineData(double.MinValue, "-1.7976931348623157e308")]
  [InlineData(double.Epsilon, "5e-324")]
  [InlineData(1e-300, "1e-300")]
  [InlineData(1e21, "1e21")]
  // "R" pads a one-digit exponent to two; the padding must not survive into the literal form.
  [InlineData(1e-9, "1e-9")]
  [InlineData(1e-5, "1e-5")]
  [InlineData(1e18, "1e18")]
  public void ToStringUsesDafnyLiteralSyntax(double value, string expected) {
    Assert.Equal(expected, new Fp64(value).ToString());
  }

  [Fact]
  public void ToStringReadsBackAsTheSameValue() {
    // The point of the formatting: every printed value is a literal denoting the value it came
    // from. Checked here with the platform parser, which is the same rounding the C# compiler
    // applies to a literal.
    foreach (var v in new[] {
      1.5, -1.5, 0.1, 1e300, 1e-300, 1e21, double.MaxValue, double.MinValue, double.Epsilon,
      Math.PI, 1.0 / 3.0, 0.0, -0.0
    }) {
      var printed = new Fp64(v).ToString();
      var back = double.Parse(printed, System.Globalization.NumberStyles.Float,
                              System.Globalization.CultureInfo.InvariantCulture);
      Assert.True(new Fp64(back) == new Fp64(v), $"{printed} did not read back as {v:R}");
    }
    foreach (var v in new[] { 1.5f, 0.1f, float.MaxValue, float.Epsilon, -0.0f }) {
      var printed = new Fp32(v).ToString();
      var back = float.Parse(printed, System.Globalization.NumberStyles.Float,
                             System.Globalization.CultureInfo.InvariantCulture);
      Assert.True(new Fp32(back) == new Fp32(v), $"{printed} did not read back as {v:R}");
    }
  }

  [Fact]
  public void Fp32BehavesLikeFp64() {
    var pos = new Fp32(0.0f);
    var neg = new Fp32(-0.0f);
    Assert.False(pos == neg);
    Assert.True(neg < pos);
    Assert.True(Fp32.IeeeEqual(pos, neg));
    Assert.True(new Fp32(float.NaN) == Fp32.FromFloatBits(unchecked((int)0x7fc00123U)));
    Assert.Equal(3, new HashSet<Fp32> {
      pos, neg, new Fp32(float.NaN), Fp32.FromFloatBits(unchecked((int)0x7fc00123U))
    }.Count);
  }

  [Fact]
  public void ArithmeticMatchesTheUnderlyingIeeeOperations() {
    var a = new Fp64(0.1);
    var b = new Fp64(0.2);
    Assert.Equal(0.1 + 0.2, (a + b).Value);
    Assert.Equal(0.1 - 0.2, (a - b).Value);
    Assert.Equal(0.1 * 0.2, (a * b).Value);
    Assert.Equal(0.1 / 0.2, (a / b).Value);
    // Negation is a sign flip, so it must move between the two zeros rather than being identity.
    Assert.True(-PosZero == NegZero);
    Assert.True(-NegZero == PosZero);
    // ... and it must not canonicalize NaN away.
    Assert.True(-NaN == NaN);
  }
}

/// <summary>
/// The classification predicates and constants must match what the verifier assumes, which is the
/// SMT-LIB FloatingPoint theory rather than System.Double's near-equivalents.
/// </summary>
public class FpClassificationTest {
  [Fact]
  public void NaNIsNeitherNegativeNorPositive() {
    // The motivating divergence: .NET's double.NaN has its sign bit set, so double.IsNegative
    // reports true for it, while fp.isNegative(NaN) is false. Dafny can observe this, because the
    // verifier proves !x.IsNegative && !x.IsPositive from x.IsNaN.
    Assert.True(double.IsNegative(double.NaN)); // what we must NOT do
    foreach (var nan in new[] {
      new Fp64(double.NaN),
      Fp64.FromDoubleBits(unchecked((long)0x7ff8000000000000UL)),
      Fp64.FromDoubleBits(unchecked((long)0xfff8000000000000UL)),
      Fp64.FromDoubleBits(unchecked((long)0x7ff0000000000001UL))
    }) {
      Assert.True(Fp64.IsNaN(nan));
      Assert.False(Fp64.IsNegative(nan));
      Assert.False(Fp64.IsPositive(nan));
      Assert.False(Fp64.IsFinite(nan));
      Assert.False(Fp64.IsInfinite(nan));
      Assert.False(Fp64.IsNormal(nan));
      Assert.False(Fp64.IsSubnormal(nan));
      Assert.False(Fp64.IsZero(nan));
    }
  }

  [Fact]
  public void SignedZerosClassifyBySignBit() {
    var pos = new Fp64(0.0);
    var neg = new Fp64(-0.0);
    Assert.True(Fp64.IsZero(pos) && Fp64.IsZero(neg));
    Assert.True(Fp64.IsPositive(pos) && !Fp64.IsNegative(pos));
    Assert.True(Fp64.IsNegative(neg) && !Fp64.IsPositive(neg));
    // Zero is neither normal nor subnormal.
    Assert.False(Fp64.IsNormal(pos) || Fp64.IsSubnormal(pos));
    Assert.False(Fp64.IsNormal(neg) || Fp64.IsSubnormal(neg));
    Assert.True(Fp64.IsFinite(pos) && Fp64.IsFinite(neg));
  }

  [Fact]
  public void NormalSubnormalAndInfinite() {
    Assert.True(Fp64.IsNormal(new Fp64(1.0)));
    Assert.True(Fp64.IsNormal(Fp64.MinNormal));
    Assert.True(Fp64.IsNormal(Fp64.MaxValue));
    Assert.True(Fp64.IsSubnormal(Fp64.MinSubnormal));
    Assert.False(Fp64.IsNormal(Fp64.MinSubnormal));
    // MinNormal is the smallest normal, so one step down is subnormal.
    Assert.True(Fp64.IsSubnormal(Fp64.FromDoubleBits(Fp64.MinNormal.ToDoubleBits() - 1)));
    Assert.True(Fp64.IsInfinite(Fp64.PositiveInfinity) && Fp64.IsInfinite(Fp64.NegativeInfinity));
    Assert.True(Fp64.IsNegative(Fp64.NegativeInfinity) && Fp64.IsPositive(Fp64.PositiveInfinity));
    Assert.False(Fp64.IsFinite(Fp64.PositiveInfinity));
  }

  [Fact]
  public void ConstantsMatchTheVerifiersExactRationals() {
    // The verifier builds these with BigFloat.FromRational on exactly these numerators and
    // denominators; if the runtime ever drifts, compiled code disagrees with what was proved.
    Assert.Equal(7074237752028440.0 / 2251799813685248.0, Fp64.Pi.Value);
    Assert.Equal(6121026514868073.0 / 2251799813685248.0, Fp64.E.Value);
    Assert.Equal(13176795f / 4194304f, Fp32.Pi.Value);
    Assert.Equal(11401300f / 4194304f, Fp32.E.Value);
    Assert.Equal(Math.Pow(2, -1022), Fp64.MinNormal.Value);
    Assert.Equal(Math.Pow(2, -1074), Fp64.MinSubnormal.Value);
    Assert.Equal(Math.Pow(2, -52), Fp64.Epsilon.Value);
    Assert.Equal((float)Math.Pow(2, -126), Fp32.MinNormal.Value);
    Assert.Equal((float)Math.Pow(2, -149), Fp32.MinSubnormal.Value);
    Assert.Equal((float)Math.Pow(2, -23), Fp32.Epsilon.Value);
    Assert.Equal(double.MaxValue, Fp64.MaxValue.Value);
    Assert.Equal(float.MaxValue, Fp32.MaxValue.Value);
  }

  [Fact]
  public void MinAndMaxIgnoreNaNRatherThanPropagateIt() {
    var nan = new Fp64(double.NaN);
    var one = new Fp64(1.5);
    // The verifier forces this: "fp.min(NaN, 1.5) != 1.5" is unsat.
    Assert.True(Fp64.Min(nan, one) == one);
    Assert.True(Fp64.Min(one, nan) == one);
    Assert.True(Fp64.Max(nan, one) == one);
    Assert.True(Fp64.Max(one, nan) == one);
    Assert.True(Fp64.IsNaN(Fp64.Min(nan, nan)));
    Assert.True(Fp64.Min(one, new Fp64(2.5)) == one);
    Assert.True(Fp64.Max(one, new Fp64(2.5)) == new Fp64(2.5));
  }

  [Fact]
  public void UncheckedBuiltInsAreIeeeNotDafny() {
    var pos = new Fp64(0.0);
    var neg = new Fp64(-0.0);
    var nan = new Fp64(double.NaN);
    // fp64.Equal / fp64.Less keep IEEE semantics; "==" and "<" do not.
    Assert.True(Fp64.Equal(pos, neg));
    Assert.False(pos == neg);
    Assert.False(Fp64.Less(neg, pos));
    Assert.True(neg < pos);
    Assert.False(Fp64.LessOrEqual(nan, nan));
    Assert.True(Fp64.GreaterOrEqual(pos, neg));
    Assert.True(Fp64.Greater(new Fp64(2.0), new Fp64(1.0)));
  }

  [Fact]
  public void RoundingBuiltIns() {
    Assert.Equal(2.0, Fp64.Round(new Fp64(2.5)).Value);   // ties to even
    Assert.Equal(2.0, Fp64.Round(new Fp64(1.5)).Value);
    Assert.Equal(1.0, Fp64.Floor(new Fp64(1.7)).Value);
    Assert.Equal(2.0, Fp64.Ceiling(new Fp64(1.2)).Value);
    Assert.Equal(1.5, Fp64.Abs(new Fp64(-1.5)).Value);
    Assert.Equal(3.0, Fp64.Sqrt(new Fp64(9.0)).Value);
    Assert.Equal(new BigInteger(-1), Fp64.ToInt(new Fp64(-1.7)));  // truncates toward zero
    Assert.Equal(new BigInteger(1), Fp64.ToInt(new Fp64(1.7)));
    Assert.Equal(2.0f, Fp32.Round(new Fp32(2.5f)).Value);
    Assert.Equal(3.0f, Fp32.Sqrt(new Fp32(9.0f)).Value);
    // fp32 Sqrt must be correctly rounded, not merely computed in double and truncated.
    for (var i = 1; i < 2000; i++) {
      var x = (float)i / 7.0f;
      Assert.Equal((float)Math.Sqrt((double)x), Fp32.Sqrt(new Fp32(x)).Value);
    }
  }
}

/// <summary>
/// "x as real" must produce the exact value, for every finite input including subnormals, and it
/// must print the way a Dafny real prints.
/// </summary>
public class FpToRealTest {
  [Theory]
  [InlineData(1.5, "3/2")]
  [InlineData(-1.5, "-3/2")]
  [InlineData(2.0, "2/1")]
  [InlineData(0.0, "0/1")]
  [InlineData(-0.0, "0/1")]     // reals have no signed zero
  [InlineData(0.25, "1/4")]
  [InlineData(-0.125, "-1/8")]
  public void ExactAndReduced(double value, string expected) {
    var r = Fp64.ToReal(new Fp64(value));
    Assert.Equal(expected, $"{r.num}/{r.den}");
  }

  [Fact]
  public void PrintsLikeADafnyReal() {
    // The unreduced form would print 1.5 with fifty-odd decimal places.
    Assert.Equal("1.5", Fp64.ToReal(new Fp64(1.5)).ToString());
    Assert.Equal("2.0", Fp64.ToReal(new Fp64(2.0)).ToString());
    Assert.Equal("-0.125", Fp64.ToReal(new Fp64(-0.125)).ToString());
  }

  [Fact]
  public void SubnormalsConvertRatherThanThrow() {
    // BigRational's double constructor rejects subnormals; the verifier proves this conversion
    // fine for every finite value, so the runtime has to handle them.
    Assert.Equal(BigInteger.One, Fp64.ToReal(Fp64.MinSubnormal).num);
    Assert.Equal(BigInteger.Pow(2, 1074), Fp64.ToReal(Fp64.MinSubnormal).den);
    Assert.Equal(BigInteger.One, Fp32.ToReal(Fp32.MinSubnormal).num);
    Assert.Equal(BigInteger.Pow(2, 149), Fp32.ToReal(Fp32.MinSubnormal).den);
    // A subnormal with several significant bits.
    var s = Fp64.FromDoubleBits(5L);
    Assert.Equal(new BigInteger(5), Fp64.ToReal(s).num);
    Assert.Equal(BigInteger.Pow(2, 1074), Fp64.ToReal(s).den);
  }

  [Fact]
  public void RoundTripsThroughReal() {
    foreach (var v in new[] {
      1.5, -1.5, 0.1, 1e300, 1e-300, double.MaxValue, double.Epsilon, 3.0, 1.0 / 3.0
    }) {
      var back = Fp64.FromReal(Fp64.ToReal(new Fp64(v)));
      Assert.True(back == new Fp64(v), $"{v} did not survive fp64 -> real -> fp64");
    }
  }

  [Fact]
  public void NonFiniteValuesAreRejected() {
    // "as real" carries a finiteness obligation, so reaching these means the proof was bypassed.
    Assert.Throws<ArgumentException>(() => Fp64.ToReal(Fp64.PositiveInfinity));
    Assert.Throws<ArgumentException>(() => Fp64.ToReal(Fp64.NaN));
  }
}

/// <summary>
/// BigRational.ToDouble and ToSingle are the runtime half of "r as fp64" and of fp64.FromReal, and
/// the verifier models that conversion as SMT-LIB's (_ to_fp) with round-to-nearest-even. So they
/// have to be correctly rounded, which they were not: they rounded the scaled quotient and then
/// rounded again when narrowing it, and rounding twice is not rounding once.
/// </summary>
public class BigRationalToFloatTest {
  /// <summary>The exact value of a finite double, as a fraction.</summary>
  private static (BigInteger, BigInteger) Exact(double value) {
    var bits = BitConverter.DoubleToInt64Bits(value);
    var biasedExponent = (int)((bits >> 52) & 0x7ff);
    var mantissa = bits & 0xfffffffffffffL;
    var significand = biasedExponent == 0 ? mantissa : mantissa | (1L << 52);
    var exponent = (biasedExponent == 0 ? 1 : biasedExponent) - 1075;
    var numerator = bits < 0 ? -new BigInteger(significand) : new BigInteger(significand);
    return exponent >= 0
      ? (numerator * BigInteger.Pow(2, exponent), BigInteger.One)
      : (numerator, BigInteger.Pow(2, -exponent));
  }

  /// <summary>
  /// Whether "candidate" is the nearest representable value to num/den, decided by exact integer
  /// arithmetic over its neighbours rather than by trusting another conversion.
  /// </summary>
  private static bool IsNearest(BigInteger num, BigInteger den, double candidate, bool single) {
    var bits = single ? BitConverter.SingleToInt32Bits((float)candidate) : BitConverter.DoubleToInt64Bits(candidate);
    BigInteger bestError = -1, bestScale = 1;
    long best = bits;
    for (long offset = -2; offset <= 2; offset++) {
      var neighbour = single
        ? (double)BitConverter.Int32BitsToSingle((int)(bits + offset))
        : BitConverter.Int64BitsToDouble(bits + offset);
      if (double.IsNaN(neighbour) || double.IsInfinity(neighbour)) {
        continue;
      }
      var (n, d) = Exact(neighbour);
      var error = BigInteger.Abs(num * d - n * den);
      var scale = den * d;
      if (bestError < 0 || error * bestScale < bestError * scale) {
        bestError = error;
        bestScale = scale;
        best = bits + offset;
      }
    }
    return best == bits;
  }

  [Fact]
  public void ToDoubleIsCorrectlyRounded() {
    var random = new Random(11);
    for (var i = 0; i < 5000; i++) {
      BigInteger num = random.Next(1, 1000000);
      BigInteger den = random.Next(1, 1000000);
      var converted = new BigRational(num, den).ToDouble();
      Assert.True(IsNearest(num, den, converted, false), $"{num}/{den} converted to {converted:R}");
    }
  }

  [Fact]
  public void ToSingleIsCorrectlyRounded() {
    var random = new Random(13);
    for (var i = 0; i < 5000; i++) {
      BigInteger num = random.Next(1, 1000000);
      BigInteger den = random.Next(1, 1000000);
      var converted = new BigRational(num, den).ToSingle();
      Assert.True(IsNearest(num, den, converted, true), $"{num}/{den} converted to {converted:R}");
    }
  }

  [Fact]
  public void RepresentableValuesConvertExactly() {
    // "r as fp64" asserts that r is exactly representable, so these are the only inputs it reaches.
    var random = new Random(5);
    for (var i = 0; i < 5000; i++) {
      var significand = (long)(random.NextDouble() * 9007199254740992L) | 1;
      var scale = random.Next(0, 60);
      var expected = significand / Math.Pow(2, scale);
      if (double.IsInfinity(expected) || expected == 0) {
        continue;
      }
      var rational = new BigRational(new BigInteger(significand), BigInteger.Pow(2, scale));
      Assert.Equal(expected, rational.ToDouble());
    }
  }

  [Fact]
  public void TheDoubleRoundingCaseThatMotivatedThis() {
    // 834650/960706 came out as 0.8687881620391671 when the quotient was rounded before narrowing;
    // the nearest double is 0.868788162039167.
    var converted = new BigRational(834650, 960706).ToDouble();
    Assert.Equal(0.868788162039167, converted);
    Assert.True(IsNearest(834650, 960706, converted, false));
  }
}
