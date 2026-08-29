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
    var anotherNaN = new Fp64(double.NaN);
    Assert.True(NaN == anotherNaN);
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
  public void NaNIsTheMaximumOfTheOrder() {
    var one = new Fp64(1.0);
    var posInf = new Fp64(double.PositiveInfinity);
    // Dafny's order is total, so a NaN operand does not make a comparison false in both
    // directions the way IEEE does. NaN is above every number, including the infinities.
    Assert.True(one < NaN);
    Assert.True(posInf < NaN);
    Assert.False(NaN < one);
    Assert.True(one <= NaN);
    Assert.False(NaN <= one);
    // Strict, so NaN is not below itself, while "<=" is reflexive there because "==" is. Spelled
    // with two variables of the same value, since these are functions of the value and comparing
    // one variable with itself only warns.
    var sameNaN = new Fp64(double.NaN);
    Assert.False(NaN < sameNaN);
    Assert.True(NaN <= sameNaN);
    Assert.False(NaN < NaNPayload);
    Assert.True(NaN <= NegNaN);
    // The IEEE predicates are unchanged: there a NaN operand is false in every direction.
    Assert.False(Fp64.IeeeLess(one, NaN));
    Assert.False(Fp64.IeeeLess(NaN, one));
    Assert.False(Fp64.IeeeLessOrEqual(one, NaN));
    Assert.False(Fp64.IeeeLessOrEqual(NaN, sameNaN));
  }

  /// <summary>
  /// Every distinct Dafny value, plus a second representative of each of the two classes where the
  /// bit pattern is not the value.
  /// </summary>
  private static readonly Fp64[] OrderSample = {
    PosZero, NegZero, NaN, NaNPayload, NegNaN, new Fp64(1.0), new Fp64(-1.0),
    new Fp64(double.PositiveInfinity), new Fp64(double.NegativeInfinity),
    new Fp64(double.Epsilon), new Fp64(-double.Epsilon),
    new Fp64(double.MaxValue), new Fp64(double.MinValue)
  };

  [Fact]
  public void HashAndComparisonCollectionsAgree() {
    var values = new[] { PosZero, NegZero, NaN, NaNPayload, NegNaN };
    // Three distinct Dafny values: -0.0, +0.0, NaN.
    Assert.Equal(3, new HashSet<Fp64>(values).Count);
    // No explicit comparer: the order is total and consistent with Equals, so the default one --
    // which is CompareTo -- is correct for a SortedSet. That is the whole reason to implement
    // IComparable rather than offer a separate comparer.
    Assert.Equal(3, new SortedSet<Fp64>(values).Count);
  }

  [Fact]
  public void CompareToIsExactlyDafnysOrder() {
    foreach (var a in OrderSample) {
      foreach (var b in OrderSample) {
        var compared = a.CompareTo(b);
        // Not merely consistent with the operators: the same relation, in all three directions.
        Assert.Equal(a < b, compared < 0);
        Assert.Equal(a == b, compared == 0);
        Assert.Equal(b < a, compared > 0);
        Assert.Equal(a <= b, compared <= 0);
        // IComparable.CompareTo must agree, and reject anything else.
        Assert.Equal(compared, ((IComparable)a).CompareTo(b));
      }
      Assert.Equal(1, ((IComparable)a).CompareTo(null));
      Assert.Throws<ArgumentException>(() => ((IComparable)a).CompareTo(1.0));
    }
  }

  /// <summary>
  /// Anchors the order to IEEE where the two are meant to agree. The axiom test below cannot do
  /// this on its own: "&lt;=", "&gt;" and "&gt;=" are all defined in terms of "&lt;", so a "&lt;" that had the
  /// whole line backwards would flip the four together and still satisfy every axiom.
  /// </summary>
  [Fact]
  public void OrderAgreesWithIeeeAwayFromNaNAndTheZeroPair() {
    foreach (var a in OrderSample) {
      foreach (var b in OrderSample) {
        if (Fp64.IsNaN(a) || Fp64.IsNaN(b)) {
          continue;                                     // NaN is where Dafny departs from IEEE
        }
        if (Fp64.IsZero(a) && Fp64.IsZero(b)) {
          continue;                                     // and the two zeros are the other place
        }
        Assert.Equal(a.Value < b.Value, a < b);
        Assert.Equal(a.Value <= b.Value, a <= b);
        Assert.Equal(a.Value > b.Value, a > b);
        Assert.Equal(a.Value >= b.Value, a >= b);
      }
    }
  }

  [Fact]
  public void OrderIsAStrictTotalOrderIncludingNaN() {
    // The five properties Z3 discharges over the verifier's encoding, checked here over the
    // compiled one, so the two cannot drift apart. Every quantifier ranges over NaN too: totality
    // is the point of the change, and it is what the partial order lacked. Both loops run over the
    // same array, so the diagonal is included and irreflexivity falls out of trichotomy there.
    foreach (var a in OrderSample) {
      foreach (var b in OrderSample) {
        Assert.True(a < b || a == b || b < a);                        // totality
        Assert.Equal(1, (a < b ? 1 : 0) + (a == b ? 1 : 0) + (b < a ? 1 : 0));  // trichotomy
        Assert.Equal(a <= b && b <= a, a == b);                       // antisymmetry
        Assert.Equal(a <= b, a < b || a == b);                        // "<=" is the closure of "<"
        Assert.Equal(a > b, b < a);
        Assert.Equal(a >= b, b <= a);
        // Only a total order satisfies these; under the earlier partial one a pair either side of
        // NaN met the right side and not the left. This is how the runtime DEFINES "<=" and ">=", so
        // here they are tautologies -- what earns their place is that the verifier defines FpAtMost
        // differently, and FpTotalOrderNeedsCaseSplitZero.dfy asserts the same two identities there.
        Assert.Equal(a <= b, !(b < a));
        Assert.Equal(a >= b, !(a < b));
        foreach (var c in OrderSample) {
          if (a < b && b < c) {
            Assert.True(a < c);                                       // transitivity
          }
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
    var nan = new Fp32(float.NaN);
    var payload = Fp32.FromFloatBits(unchecked((int)0x7fc00123U));
    Assert.False(pos == neg);
    Assert.True(neg < pos);
    Assert.True(Fp32.IeeeEqual(pos, neg));
    Assert.True(nan == payload);
    Assert.Equal(3, new HashSet<Fp32> { pos, neg, nan, payload }.Count);
    // The order is total here too, with NaN at the top.
    Assert.True(new Fp32(float.PositiveInfinity) < nan);
    Assert.False(nan < pos);
    Assert.True(nan <= payload);
    Assert.False(Fp32.IeeeLess(pos, nan));
    Assert.Equal(0, nan.CompareTo(payload));
    Assert.True(pos.CompareTo(nan) < 0);
    Assert.Equal(3, new SortedSet<Fp32> { pos, neg, nan, payload }.Count);
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
  public void Fp32ClassifiesLikeFp64() {
    // The classification predicates are written out per width, so Fp64 passing says nothing about
    // Fp32. The NaN-sign hazard is the reason: System.Single.IsNegative reports the sign bit, and
    // float.NaN carries it, so delegating would answer true where fp.isNegative answers false.
    Assert.True(float.IsNegative(float.NaN)); // what must NOT be delegated to
    foreach (var nan in new[] {
      new Fp32(float.NaN),
      Fp32.FromFloatBits(unchecked((int)0x7fc00000U)),
      Fp32.FromFloatBits(unchecked((int)0xffc00000U)),
      Fp32.FromFloatBits(unchecked((int)0x7f800001U))
    }) {
      Assert.True(Fp32.IsNaN(nan));
      Assert.False(Fp32.IsNegative(nan));
      Assert.False(Fp32.IsPositive(nan));
      Assert.False(Fp32.IsFinite(nan));
      Assert.False(Fp32.IsInfinite(nan));
      Assert.False(Fp32.IsNormal(nan));
      Assert.False(Fp32.IsSubnormal(nan));
      Assert.False(Fp32.IsZero(nan));
    }

    var pos = new Fp32(0.0f);
    var neg = new Fp32(-0.0f);
    Assert.True(Fp32.IsZero(pos) && Fp32.IsZero(neg));
    Assert.True(Fp32.IsPositive(pos) && !Fp32.IsNegative(pos));
    Assert.True(Fp32.IsNegative(neg) && !Fp32.IsPositive(neg));
    Assert.False(Fp32.IsNormal(pos) || Fp32.IsSubnormal(pos));

    Assert.True(Fp32.IsNormal(new Fp32(1.0f)));
    Assert.True(Fp32.IsNormal(Fp32.MinNormal));
    Assert.True(Fp32.IsSubnormal(Fp32.MinSubnormal));
    Assert.False(Fp32.IsNormal(Fp32.MinSubnormal));
    Assert.True(Fp32.IsSubnormal(Fp32.FromFloatBits(Fp32.MinNormal.ToFloatBits() - 1)));
    Assert.True(Fp32.IsInfinite(Fp32.PositiveInfinity) && Fp32.IsNegative(Fp32.NegativeInfinity));

    // And the unchecked family keeps IEEE at this width too.
    Assert.True(Fp32.Equal(pos, neg));
    Assert.False(pos == neg);
    Assert.False(Fp32.Less(neg, pos));
    Assert.True(neg < pos);
    Assert.True(Fp32.Min(new Fp32(float.NaN), new Fp32(1.5f)) == new Fp32(1.5f));
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
    // fp32 Sqrt computes in double and rounds back, which the implementation argues is correctly
    // rounded because double carries at least 2p+2 bits. Check that against an oracle that never
    // takes a square root: the result is nearest iff x lies between the squares of the midpoints to
    // its two neighbours, which is exact integer arithmetic over the floats' own values. Comparing
    // against (float)Math.Sqrt((double)x) instead would just restate the implementation.
    for (var i = 1; i < 3000; i++) {
      var x = (float)i / 7.0f;
      var root = Fp32.Sqrt(new Fp32(x)).Value;
      Assert.True(IsCorrectlyRoundedSqrt(x, root), $"sqrt({x:R}) gave {root:R}");
    }
    // The oracle has to have teeth, or this test is as empty as comparing against the
    // implementation: a root off by one step in either direction must be rejected.
    for (var i = 1; i < 200; i++) {
      var x = (float)i / 7.0f;
      var bits = BitConverter.SingleToInt32Bits(Fp32.Sqrt(new Fp32(x)).Value);
      Assert.False(IsCorrectlyRoundedSqrt(x, BitConverter.Int32BitsToSingle(bits + 1)),
        $"the oracle accepted a root one step above the correct one for {x:R}");
      Assert.False(IsCorrectlyRoundedSqrt(x, BitConverter.Int32BitsToSingle(bits - 1)),
        $"the oracle accepted a root one step below the correct one for {x:R}");
    }
  }

  /// <summary>The exact value of a finite float, as a fraction.</summary>
  private static (BigInteger, BigInteger) ExactSingle(float value) {
    var bits = BitConverter.SingleToInt32Bits(value);
    var biasedExponent = (bits >> 23) & 0xff;
    var mantissa = bits & 0x7fffff;
    var significand = biasedExponent == 0 ? mantissa : mantissa | (1 << 23);
    var exponent = (biasedExponent == 0 ? 1 : biasedExponent) - 150;
    BigInteger numerator = significand;
    return exponent >= 0
      ? (numerator * BigInteger.Pow(2, exponent), BigInteger.One)
      : (numerator, BigInteger.Pow(2, -exponent));
  }

  /// <summary>
  /// Whether "root" is the nearest float to the square root of "x", decided by squaring rather than
  /// by rooting. The midpoint between "root" and a neighbour is exact, so comparing its square
  /// against x says which side of the rounding boundary x falls on.
  /// </summary>
  private static bool IsCorrectlyRoundedSqrt(float x, float root) {
    if (x == 0.0f || float.IsInfinity(x)) {
      return root == x;
    }
    var (xn, xd) = ExactSingle(x);
    var bits = BitConverter.SingleToInt32Bits(root);

    // sign of (midpoint(root, neighbour)^2 - x)
    int MidpointSquaredVersusX(int neighbourBits) {
      var (an, ad) = ExactSingle(root);
      var (bn, bd) = ExactSingle(BitConverter.Int32BitsToSingle(neighbourBits));
      var mn = an * bd + bn * ad;      // midpoint = mn / md
      var md = 2 * ad * bd;
      return (mn * mn * xd).CompareTo(xn * md * md);
    }

    // x must not be below the lower boundary, nor above the upper one.
    var aboveLower = bits == 0 || MidpointSquaredVersusX(bits - 1) <= 0;
    var belowUpper = MidpointSquaredVersusX(bits + 1) >= 0;
    return aboveLower && belowUpper;
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
  public void CorrectlyRoundedAcrossTheExponentRange() {
    // The two tests above draw numerator and denominator from [1, 1000000), so every sample lands in
    // [1e-6, 1e6] and neither can see underflow or overflow. Scaling by powers of ten reaches the
    // subnormal range, far underflow, and overflow -- where a value hundreds of binades below the
    // smallest subnormal was coming back AS the smallest subnormal instead of zero.
    var random = new Random(17);
    foreach (var scale in new[] { 0, 30, 100, 200, 300, 310, 320, 324, 330, 400 }) {
      for (var i = 0; i < 200; i++) {
        BigInteger num = random.Next(1, 1000);
        var den = new BigInteger(random.Next(1, 1000)) * BigInteger.Pow(10, scale);
        var small = new BigRational(num, den).ToDouble();
        Assert.True(IsNearest(num, den, small, false), $"{num}/({den}) converted to {small:R}");
        // And the same magnitudes upward: either the value overflows to infinity, or it is finite and
        // must still be the nearest representable one.
        BigInteger bigNum = num * BigInteger.Pow(10, scale);
        BigInteger bigDen = random.Next(1, 1000);
        var big = new BigRational(bigNum, bigDen).ToDouble();
        Assert.False(double.IsNaN(big));
        if (!double.IsInfinity(big)) {
          Assert.True(IsNearest(bigNum, bigDen, big, false), $"{bigNum}/{bigDen} converted to {big:R}");
        }
      }
    }
    // The specific values that were wrong, at both widths.
    Assert.Equal(0.0, new BigRational(1, BigInteger.Pow(10, 400)).ToDouble());
    Assert.Equal(0.0f, new BigRational(1, BigInteger.Pow(10, 60)).ToSingle());
    // A genuine subnormal must survive.
    Assert.True(new BigRational(1, BigInteger.Pow(10, 320)).ToDouble() > 0.0);
    Assert.True(Fp64.IsSubnormal(new Fp64(new BigRational(1, BigInteger.Pow(10, 320)).ToDouble())));
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
