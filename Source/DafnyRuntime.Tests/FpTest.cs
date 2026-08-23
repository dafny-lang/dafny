using System.Collections.Generic;
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
