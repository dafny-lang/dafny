//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

// When --include-runtime is true, this file is directly prepended
// to the output program. We have to avoid these using directives in that case
// since they can only appear before any other declarations.
// The DafnyRuntime.csproj file is the only place that ISDAFNYRUNTIMELIB is defined,
// so these are only active when building the C# DafnyRuntime.dll library.
#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
using System.Collections;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  // Similar to System.Text.Rune, which would be perfect to use
  // except that it isn't available in the platforms we support
  // (.NET Standard 2.0 and .NET Framework 4.5.2)
  public readonly struct Rune : IComparable, IComparable<Rune>, IEquatable<Rune> {

    private readonly uint _value;

    public Rune(int value)
      : this((uint)value) {
    }

    public Rune(uint value) {
      if (!(value < 0xD800 || (0xE000 <= value && value < 0x11_0000))) {
        throw new ArgumentException();
      }

      _value = value;
    }

    public static bool IsRune(BigInteger i) {
      return (0 <= i && i < 0xD800) || (0xE000 <= i && i < 0x11_0000);
    }

    public int Value => (int)_value;

    public bool Equals(Rune other) => this == other;

    public override bool Equals(object obj) => (obj is Rune other) && Equals(other);

    public override int GetHashCode() => Value;

    // Values are always between 0 and 0x11_0000, so overflow isn't possible
    public int CompareTo(Rune other) => this.Value - other.Value;

    int IComparable.CompareTo(object obj) {
      switch (obj) {
        case null:
          return 1; // non-null ("this") always sorts after null
        case Rune other:
          return CompareTo(other);
        default:
          throw new ArgumentException();
      }
    }

    public static bool operator ==(Rune left, Rune right) => left._value == right._value;

    public static bool operator !=(Rune left, Rune right) => left._value != right._value;

    public static bool operator <(Rune left, Rune right) => left._value < right._value;

    public static bool operator <=(Rune left, Rune right) => left._value <= right._value;

    public static bool operator >(Rune left, Rune right) => left._value > right._value;

    public static bool operator >=(Rune left, Rune right) => left._value >= right._value;

    public static explicit operator Rune(int value) => new Rune(value);
    public static explicit operator Rune(BigInteger value) => new Rune((uint)value);

    // Defined this way to be consistent with System.Text.Rune,
    // but note that Dafny will use Helpers.ToString(rune),
    // which will print in the style of a character literal instead.
    public override string ToString() {
      return char.ConvertFromUtf32(Value);
    }

    // Replacement for String.EnumerateRunes() from newer platforms
    public static IEnumerable<Rune> Enumerate(string s) {
      var sLength = s.Length;
      for (var i = 0; i < sLength; i++) {
        if (char.IsHighSurrogate(s[i])) {
          if (char.IsLowSurrogate(s[i + 1])) {
            yield return (Rune)char.ConvertToUtf32(s[i], s[i + 1]);
            i++;
          } else {
            throw new ArgumentException();
          }
        } else if (char.IsLowSurrogate(s[i])) {
          throw new ArgumentException();
        } else {
          yield return (Rune)s[i];
        }
      }
    }
  }

  // ---------------------------------------------------------------------------
  // Dafny's fp32/fp64 are value identity on the SMT FloatingPoint sort: there is
  // exactly one NaN, and +0.0 and -0.0 are distinct. C#'s float/double reproduce
  // neither -- "==" is IEEE (NaN != NaN, +0.0 == -0.0) and Equals is a third
  // relation again (NaN == NaN and +0.0 == -0.0). So fp values are represented by
  // these wrappers, whose Equals/GetHashCode implement the verifier's semantics
  // and whose arithmetic delegates to float/double.
  //
  // The wrapped value is stored VERBATIM; NaN payloads are never rewritten.
  // Canonicalization happens only in EqualityKey, the one place that observes it.
  // The struct therefore has NO representation invariant, which is what makes it
  // safe against MemoryMarshal.Cast and other bit-level interop: Equals is a
  // function of the bit pattern that is constant on each equivalence class, so
  // any representative gives the same answer.
  //
  // IComparable is implemented, and is Dafny's own order rather than an
  // approximation of it: the order is total, including at NaN, so .NET's
  // requirement that CompareTo be a total order consistent with Equals is met
  // exactly.
  //
  // This file compiles against netstandard2.0 and net452 at LangVersion 7.3, so
  // double.IsNegative/IsFinite/IsNormal/IsSubnormal and
  // BitConverter.SingleToInt32Bits are unavailable here.
  // ---------------------------------------------------------------------------
  /// <summary>
  /// Renders what "R" produced in the way Dafny writes a floating-point literal, so that printed
  /// output can be read back as source: a lowercase exponent marker with no "+", and a decimal
  /// point when there is no exponent at all. "R" already gives the shortest digits that identify
  /// the value, which are the same digits Dafny's own literal printer produces, so only the
  /// punctuation differs.
  /// </summary>
  internal static class FpFormat {
    internal static string DafnyLiteralForm(string rendered) {
      var s = rendered.Replace("E+", "e").Replace("E", "e");
      var marker = s.IndexOf('e');
      if (marker < 0) {
        return s.IndexOf('.') < 0 ? s + ".0" : s;
      }
      // "R" pads an exponent to two digits, so 1e-9 arrives as 1e-09. Strip the padding: an
      // unpadded exponent is how a Dafny literal is written, and how every other shortest-form
      // printer renders it.
      var exponent = s.Substring(marker + 1);
      var sign = exponent.Length > 0 && exponent[0] == '-' ? "-" : "";
      var digits = (sign.Length > 0 ? exponent.Substring(1) : exponent).TrimStart('0');
      return s.Substring(0, marker + 1) + sign + (digits.Length == 0 ? "0" : digits);
    }
  }

  public readonly struct Fp64 : IEquatable<Fp64>, IComparable<Fp64>, IComparable {
    private readonly double value;

    private const long NaNCanonicalBits = unchecked((long)0x7ff8000000000000UL);
    private const long SignBit = unchecked((long)0x8000000000000000UL);
    private const long ExponentMask = unchecked((long)0x7ff0000000000000UL);
    private const long SignificandMask = unchecked((long)0x000fffffffffffffUL);

    public Fp64(double value) { this.value = value; }

    public double Value => value;

    public static Fp64 FromDoubleBits(long bits) => new Fp64(BitConverter.Int64BitsToDouble(bits));
    public long ToDoubleBits() => BitConverter.DoubleToInt64Bits(value);

    public static readonly Fp64 Zero = new Fp64(0.0);

    /// <summary>
    /// This value's identity in the SMT FloatingPoint sort: the raw bits, except that every NaN
    /// maps to one pattern. Two Fp64s are the same Dafny value exactly when their keys are equal.
    /// </summary>
    private static bool IsNaNBits(long bits) =>
      (bits & ExponentMask) == ExponentMask && (bits & SignificandMask) != 0;

    private long EqualityKey => IsNaNBits(BitConverter.DoubleToInt64Bits(value))
      ? NaNCanonicalBits
      : BitConverter.DoubleToInt64Bits(value);

    public bool Equals(Fp64 other) {
      var a = BitConverter.DoubleToInt64Bits(value);
      var b = BitConverter.DoubleToInt64Bits(other.value);
      // Equal bit patterns are the same value. Differing ones can still be the same value only
      // when both are NaN, because the sort has exactly one NaN -- that is the entire difference
      // between this and comparing the raw doubles.
      return a == b || (IsNaNBits(a) && IsNaNBits(b));
    }
    public override bool Equals(object obj) => obj is Fp64 other && Equals(other);
    public override int GetHashCode() => EqualityKey.GetHashCode();

    // Dafny's "==". NOT IEEE equality; fp64.Equal maps to IeeeEqual below.
    public static bool operator ==(Fp64 a, Fp64 b) => a.Equals(b);
    public static bool operator !=(Fp64 a, Fp64 b) => !a.Equals(b);

    // fp64.Equal: IEEE fp.eq.
    public static bool IeeeEqual(Fp64 a, Fp64 b) => a.value == b.value;

    private bool IsNegativeZero => BitConverter.DoubleToInt64Bits(value) == SignBit;
    private bool IsPositiveZero => BitConverter.DoubleToInt64Bits(value) == 0L;

    // Dafny's "<": IEEE fp.lt refined so that -0.0 < +0.0 and so that NaN is above every number.
    // Mirrors FpLess in the verifier, where the reasons for both refinements are set out. The result
    // is a strict total order agreeing with "==", so unlike IEEE it is defined on every pair --
    // 1.0 < NaN is true and NaN < NaN is false.
    //
    // The NaN test is double.IsNaN rather than the bit form used by IsNaN below. The two agree on
    // every input, unlike double.IsNegative, and double.IsNaN is "d != d", a single compare where
    // the bit form needs a reinterpret and two masks. Over 60M comparisons on non-NaN data the bit
    // form cost about 4% against the earlier partial order, and this form nothing measurable.
    public static bool operator <(Fp64 a, Fp64 b) =>
      a.value < b.value || (a.IsNegativeZero && b.IsPositiveZero)
                        || (!double.IsNaN(a.value) && double.IsNaN(b.value));

    // The other three follow from that one, because the order is total: "a <= b" and "not (b < a)"
    // agree everywhere, which they did not under the earlier partial order. Measured to cost nothing
    // over spelling "<=" out separately, and it leaves one definition to get right.
    //
    // The verifier's FpAtMost deliberately does NOT take this shortcut, for a reason that applies
    // only there: it turns antisymmetry into trichotomy, which Dafny's default solver options cannot
    // discharge. See FpAtMost. What holds the two spellings to the same order is FpCoherentOrder.dfy,
    // plus the complement identity in FpTotalOrderNeedsCaseSplitZero.dfy.
    public static bool operator >(Fp64 a, Fp64 b) => b < a;
    public static bool operator <=(Fp64 a, Fp64 b) => !(b < a);
    public static bool operator >=(Fp64 a, Fp64 b) => !(a < b);

    // fp64.Less and friends keep raw IEEE, mirroring fp64.Equal versus "==".
    public static bool IeeeLess(Fp64 a, Fp64 b) => a.value < b.value;
    public static bool IeeeLessOrEqual(Fp64 a, Fp64 b) => a.value <= b.value;

    public static Fp64 operator +(Fp64 a, Fp64 b) => new Fp64(a.value + b.value);
    public static Fp64 operator -(Fp64 a, Fp64 b) => new Fp64(a.value - b.value);
    public static Fp64 operator *(Fp64 a, Fp64 b) => new Fp64(a.value * b.value);
    public static Fp64 operator /(Fp64 a, Fp64 b) => new Fp64(a.value / b.value);
    public static Fp64 operator -(Fp64 a) => new Fp64(-a.value);

    public static explicit operator double(Fp64 a) => a.value;
    public static explicit operator Fp64(double d) => new Fp64(d);

    [Obsolete("Compare Dafny.Fp64 with Dafny.Fp64; wrap the double as new Dafny.Fp64(d).", true)]
    public bool Equals(double other) => throw new NotSupportedException();

    /// <summary>
    /// Dafny's order, as .NET's comparison protocol. This is exactly the order the operators above
    /// implement, so CompareTo is negative precisely where "&lt;" holds and zero precisely where
    /// Equals holds -- which is what a SortedSet or SortedDictionary requires, and what makes
    /// Comparer&lt;Fp64&gt;.Default correct for one.
    ///
    /// The key is computed from the CANONICALIZED value, so all NaN payloads and both NaN signs
    /// share the single position at the top.
    ///
    /// This differs from fp64's platform counterpart. System.Double.CompareTo returns 0 for the two
    /// zeros, so it is inconsistent with an equality that separates them, and it places NaN BELOW
    /// negative infinity. java.lang.Double.compare is the same shape as this one, NaN at the top
    /// included.
    /// </summary>
    public int CompareTo(Fp64 other) => OrderKey(this).CompareTo(OrderKey(other));

    int IComparable.CompareTo(object obj) {
      if (obj == null) {
        return 1;
      }
      if (obj is Fp64 other) {
        return CompareTo(other);
      }
      throw new ArgumentException("Expected a Dafny.Fp64", nameof(obj));
    }

    private static long OrderKey(Fp64 v) {
      // Map sign-magnitude onto a monotone two's-complement key. The "- 1" is what keeps -0.0
      // strictly below +0.0; without it the two collide and SortedSet disagrees with HashSet. The
      // canonical NaN pattern exceeds +infinity's, so NaN lands at the top with nothing to do.
      var bits = v.EqualityKey;
      return bits < 0 ? long.MinValue - bits - 1 : bits;
    }

    // -------- Classification --------
    // These are the SMT-LIB FloatingPoint predicates, which is what the verifier reasons about.
    // They are spelled out over the bits rather than delegated to System.double for two reasons:
    // double.IsNormal/IsSubnormal do not exist on every target framework of this library, and
    // double.IsNegative disagrees with fp.isNegative on NaN. .NET's double.NaN has its sign bit set,
    // so double.IsNegative(double.NaN) is true, whereas SMT-LIB and IEEE 754 agree that NaN is
    // neither negative nor positive. That divergence is observable from Dafny: the verifier
    // proves !x.IsNegative from x.IsNaN.
    private static long Exponent(double d) => BitConverter.DoubleToInt64Bits(d) & ExponentMask;
    private static long Significand(double d) => BitConverter.DoubleToInt64Bits(d) & SignificandMask;

    public static bool IsNaN(Fp64 a) => IsNaNBits(BitConverter.DoubleToInt64Bits(a.value));
    public static bool IsInfinite(Fp64 a) => Exponent(a.value) == ExponentMask && Significand(a.value) == 0;
    public static bool IsFinite(Fp64 a) => Exponent(a.value) != ExponentMask;
    public static bool IsZero(Fp64 a) => Exponent(a.value) == 0 && Significand(a.value) == 0;
    public static bool IsSubnormal(Fp64 a) => Exponent(a.value) == 0 && Significand(a.value) != 0;
    public static bool IsNormal(Fp64 a) => Exponent(a.value) != 0 && Exponent(a.value) != ExponentMask;
    public static bool IsNegative(Fp64 a) => !IsNaN(a) && (BitConverter.DoubleToInt64Bits(a.value) & SignBit) != 0;
    public static bool IsPositive(Fp64 a) => !IsNaN(a) && (BitConverter.DoubleToInt64Bits(a.value) & SignBit) == 0;

    // -------- Constants --------
    // Pi and E are the exact dyadic rationals the verifier uses (see the fp64 cases in
    // BoogieGenerator.ExpressionTranslator). Numerator and denominator are each exactly
    // representable and the denominator is a power of two, so the quotient is exact: runtime and
    // verifier agree by construction rather than by how a decimal literal happens to round.
    public static readonly Fp64 NaN = FromDoubleBits(NaNCanonicalBits);
    public static readonly Fp64 PositiveInfinity = new Fp64(double.PositiveInfinity);
    public static readonly Fp64 NegativeInfinity = new Fp64(double.NegativeInfinity);
    public static readonly Fp64 Pi = new Fp64(7074237752028440.0 / 2251799813685248.0);  // / 2^51
    public static readonly Fp64 E = new Fp64(6121026514868073.0 / 2251799813685248.0);  // / 2^51
    public static readonly Fp64 MaxValue = new Fp64(double.MaxValue);
    public static readonly Fp64 MinValue = new Fp64(double.MinValue);
    public static readonly Fp64 MinNormal = FromDoubleBits(0x0010000000000000L);  // 2^-1022
    public static readonly Fp64 MinSubnormal = FromDoubleBits(1L);  // 2^-1074
    public static readonly Fp64 Epsilon = new Fp64(1.0 / 4503599627370496.0);  // 2^-52

    // -------- The fp64.* built-ins --------
    // The code generator emits a call to the static of the same name for each of these, so this is
    // the single place where their meaning is defined. Equal and Less are IEEE while the operators
    // above are Dafny's; having both under names of their own is what stops one being emitted
    // where the other was meant.
    public static bool Equal(Fp64 a, Fp64 b) => IeeeEqual(a, b);
    public static bool Less(Fp64 a, Fp64 b) => IeeeLess(a, b);
    public static bool LessOrEqual(Fp64 a, Fp64 b) => IeeeLessOrEqual(a, b);
    public static bool Greater(Fp64 a, Fp64 b) => IeeeLess(b, a);
    public static bool GreaterOrEqual(Fp64 a, Fp64 b) => IeeeLessOrEqual(b, a);

    public static Fp64 Add(Fp64 a, Fp64 b) => a + b;
    public static Fp64 Sub(Fp64 a, Fp64 b) => a - b;
    public static Fp64 Mul(Fp64 a, Fp64 b) => a * b;
    public static Fp64 Div(Fp64 a, Fp64 b) => a / b;
    public static Fp64 Neg(Fp64 a) => -a;

    public static Fp64 Abs(Fp64 a) => new Fp64(Math.Abs(a.value));
    public static Fp64 Floor(Fp64 a) => new Fp64(Math.Floor(a.value));
    public static Fp64 Ceiling(Fp64 a) => new Fp64(Math.Ceiling(a.value));
    public static Fp64 Round(Fp64 a) => new Fp64(Math.Round(a.value, MidpointRounding.ToEven));
    public static Fp64 Sqrt(Fp64 a) => new Fp64(Math.Sqrt(a.value));
    public static Fp64 FromReal(BigRational r) => new Fp64(r.ToDouble());

    // SMT-LIB fp.min/fp.max return the other operand when one is NaN instead of propagating it
    // the way Math.Min/Math.Max do, and the verifier relies on that: fp.min(NaN, 1.0) == 1.0 is
    // forced. Their value on the two zeros is left unspecified by SMT-LIB, so either is sound.
    public static Fp64 Min(Fp64 a, Fp64 b) => IsNaN(a) ? b : IsNaN(b) ? a : new Fp64(Math.Min(a.value, b.value));
    public static Fp64 Max(Fp64 a, Fp64 b) => IsNaN(a) ? b : IsNaN(b) ? a : new Fp64(Math.Max(a.value, b.value));

    public static BigInteger ToInt(Fp64 a) => (BigInteger)Math.Truncate((double)a.value);

    // The "as" conversions. Each rounds, and each is only ever emitted where the verifier has
    // already discharged an exactness obligation, so on any execution that was proved correct the
    // rounding is the identity.
    public static Fp64 FromInt(BigInteger i) => new Fp64((double)i);
    /// <summary>
    /// The exact value as a rational. Every finite fp64 is m * 2^e for integers m and e, so no
    /// approximation is involved. This does not go through BigRational's double constructor, which
    /// rejects subnormals outright and leaves the fraction unreduced -- 1.5 would come back as
    /// 2^52*3 over 2^53 and print with fifty-odd decimal places.
    /// </summary>
    public static BigRational ToReal(Fp64 a) {
      if (!IsFinite(a)) {
        throw new ArgumentException("Can't convert " + a + " to a rational.");
      }
      // Required, and not only because reals have no signed zero so that -0.0 has to land here too:
      // the reduction loop below shifts while the low bit is clear, which never terminates on a zero
      // significand. Removing this branch hangs on BOTH zeros rather than answering wrongly.
      if (IsZero(a)) {
        return new BigRational(0);
      }
      var bits = BitConverter.DoubleToInt64Bits(a.value);
      var biasedExponent = (int)((bits & ExponentMask) >> 52);
      var mantissa = bits & SignificandMask;
      // Subnormals have no implicit leading one, and their exponent is that of the smallest normal.
      var significand = biasedExponent == 0 ? mantissa : mantissa | (SignificandMask + 1);
      var exponent = (biasedExponent == 0 ? 1 : biasedExponent) - 1075;
      // Cancel the common powers of two, so 1.5 comes out as 3/2. Terminates because the significand
      // is nonzero here, per the guard above.
      while ((significand & 1) == 0) {
        significand >>= 1;
        exponent++;
      }
      var value = (bits & SignBit) != 0 ? -new BigInteger(significand) : new BigInteger(significand);
      return exponent >= 0
        ? new BigRational(value * BigInteger.Pow(2, exponent), BigInteger.One)
        : new BigRational(value, BigInteger.Pow(2, -exponent));
    }
    // Widening, which is exact for every fp32 value.
    public static Fp64 FromFp32(Fp32 a) => new Fp64((double)a.Value);

    public override string ToString() {
      if (double.IsNaN(value)) { return "NaN"; }
      if (double.IsPositiveInfinity(value)) { return "Infinity"; }
      if (double.IsNegativeInfinity(value)) { return "-Infinity"; }
      // Spelled out because .NET Framework's "R" drops the sign on negative zero, and here the
      // sign is the whole difference between two distinct Dafny values.
      if (IsNegativeZero) { return "-0.0"; }
      return FpFormat.DafnyLiteralForm(value.ToString("R", System.Globalization.CultureInfo.InvariantCulture));
    }
  }

  public readonly struct Fp32 : IEquatable<Fp32>, IComparable<Fp32>, IComparable {
    private readonly float value;

    private const int NaNCanonicalBits = unchecked((int)0x7fc00000U);
    private const int SignBit = unchecked((int)0x80000000U);
    private const int ExponentMask = unchecked((int)0x7f800000U);
    private const int SignificandMask = unchecked((int)0x007fffffU);

    // netstandard2.0 has no BitConverter.SingleToInt32Bits, and going via GetBytes would allocate
    // on every comparison, so reinterpret through an explicit-layout union.
    [System.Runtime.InteropServices.StructLayout(System.Runtime.InteropServices.LayoutKind.Explicit)]
    private struct Bits {
      [System.Runtime.InteropServices.FieldOffset(0)] public float F;
      [System.Runtime.InteropServices.FieldOffset(0)] public int I;
    }

    private static int ToBits(float f) { var b = new Bits(); b.F = f; return b.I; }
    private static float OfBits(int i) { var b = new Bits(); b.I = i; return b.F; }

    public Fp32(float value) { this.value = value; }

    public float Value => value;

    public static Fp32 FromFloatBits(int bits) => new Fp32(OfBits(bits));
    public int ToFloatBits() => ToBits(value);

    public static readonly Fp32 Zero = new Fp32(0.0f);

    private static bool IsNaNBits(int bits) =>
      (bits & ExponentMask) == ExponentMask && (bits & SignificandMask) != 0;

    private int EqualityKey => IsNaNBits(ToBits(value)) ? NaNCanonicalBits : ToBits(value);

    public bool Equals(Fp32 other) {
      var a = ToBits(value);
      var b = ToBits(other.value);
      // See Fp64.Equals: only NaNs can differ in bits and still be the same value.
      return a == b || (IsNaNBits(a) && IsNaNBits(b));
    }
    public override bool Equals(object obj) => obj is Fp32 other && Equals(other);
    public override int GetHashCode() => EqualityKey.GetHashCode();

    public static bool operator ==(Fp32 a, Fp32 b) => a.Equals(b);
    public static bool operator !=(Fp32 a, Fp32 b) => !a.Equals(b);

    public static bool IeeeEqual(Fp32 a, Fp32 b) => a.value == b.value;

    private bool IsNegativeZero => ToBits(value) == SignBit;
    private bool IsPositiveZero => ToBits(value) == 0;

    // As Fp64: a strict total order agreeing with "==", with -0.0 below +0.0 and NaN at the top;
    // float.IsNaN for the same reason given there, and the other three derived by totality.
    public static bool operator <(Fp32 a, Fp32 b) =>
      a.value < b.value || (a.IsNegativeZero && b.IsPositiveZero)
                        || (!float.IsNaN(a.value) && float.IsNaN(b.value));
    public static bool operator >(Fp32 a, Fp32 b) => b < a;
    public static bool operator <=(Fp32 a, Fp32 b) => !(b < a);
    public static bool operator >=(Fp32 a, Fp32 b) => !(a < b);

    public static bool IeeeLess(Fp32 a, Fp32 b) => a.value < b.value;
    public static bool IeeeLessOrEqual(Fp32 a, Fp32 b) => a.value <= b.value;

    public static Fp32 operator +(Fp32 a, Fp32 b) => new Fp32(a.value + b.value);
    public static Fp32 operator -(Fp32 a, Fp32 b) => new Fp32(a.value - b.value);
    public static Fp32 operator *(Fp32 a, Fp32 b) => new Fp32(a.value * b.value);
    public static Fp32 operator /(Fp32 a, Fp32 b) => new Fp32(a.value / b.value);
    public static Fp32 operator -(Fp32 a) => new Fp32(-a.value);

    public static explicit operator float(Fp32 a) => a.value;
    public static explicit operator Fp32(float f) => new Fp32(f);

    [Obsolete("Compare Dafny.Fp32 with Dafny.Fp32; wrap the float as new Dafny.Fp32(f).", true)]
    public bool Equals(float other) => throw new NotSupportedException();

    /// <summary>As Fp64.CompareTo, including why NaN sits above every number here and below every
    /// number in System.Single.CompareTo.</summary>
    public int CompareTo(Fp32 other) => OrderKey(this).CompareTo(OrderKey(other));

    int IComparable.CompareTo(object obj) {
      if (obj == null) {
        return 1;
      }
      if (obj is Fp32 other) {
        return CompareTo(other);
      }
      throw new ArgumentException("Expected a Dafny.Fp32", nameof(obj));
    }

    private static int OrderKey(Fp32 v) {
      var bits = v.EqualityKey;
      return bits < 0 ? int.MinValue - bits - 1 : bits;
    }

    // -------- Classification --------
    // These are the SMT-LIB FloatingPoint predicates, which is what the verifier reasons about.
    // They are spelled out over the bits rather than delegated to System.float for two reasons:
    // float.IsNormal/IsSubnormal do not exist on every target framework of this library, and
    // float.IsNegative disagrees with fp.isNegative on NaN. .NET's float.NaN has its sign bit set,
    // so float.IsNegative(float.NaN) is true, whereas SMT-LIB and IEEE 754 agree that NaN is
    // neither negative nor positive. That divergence is observable from Dafny: the verifier
    // proves !x.IsNegative from x.IsNaN.
    private static int Exponent(float d) => ToBits(d) & ExponentMask;
    private static int Significand(float d) => ToBits(d) & SignificandMask;

    public static bool IsNaN(Fp32 a) => IsNaNBits(ToBits(a.value));
    public static bool IsInfinite(Fp32 a) => Exponent(a.value) == ExponentMask && Significand(a.value) == 0;
    public static bool IsFinite(Fp32 a) => Exponent(a.value) != ExponentMask;
    public static bool IsZero(Fp32 a) => Exponent(a.value) == 0 && Significand(a.value) == 0;
    public static bool IsSubnormal(Fp32 a) => Exponent(a.value) == 0 && Significand(a.value) != 0;
    public static bool IsNormal(Fp32 a) => Exponent(a.value) != 0 && Exponent(a.value) != ExponentMask;
    public static bool IsNegative(Fp32 a) => !IsNaN(a) && (ToBits(a.value) & SignBit) != 0;
    public static bool IsPositive(Fp32 a) => !IsNaN(a) && (ToBits(a.value) & SignBit) == 0;

    // -------- Constants --------
    // Pi and E are the exact dyadic rationals the verifier uses (see the fp32 cases in
    // BoogieGenerator.ExpressionTranslator). Numerator and denominator are each exactly
    // representable and the denominator is a power of two, so the quotient is exact: runtime and
    // verifier agree by construction rather than by how a decimal literal happens to round.
    public static readonly Fp32 NaN = FromFloatBits(NaNCanonicalBits);
    public static readonly Fp32 PositiveInfinity = new Fp32(float.PositiveInfinity);
    public static readonly Fp32 NegativeInfinity = new Fp32(float.NegativeInfinity);
    public static readonly Fp32 Pi = new Fp32(13176795f / 4194304f);  // / 2^22
    public static readonly Fp32 E = new Fp32(11401300f / 4194304f);  // / 2^22
    public static readonly Fp32 MaxValue = new Fp32(float.MaxValue);
    public static readonly Fp32 MinValue = new Fp32(float.MinValue);
    public static readonly Fp32 MinNormal = FromFloatBits(0x00800000);  // 2^-126
    public static readonly Fp32 MinSubnormal = FromFloatBits(1);  // 2^-149
    public static readonly Fp32 Epsilon = new Fp32(1.0f / 8388608.0f);  // 2^-23

    // -------- The fp32.* built-ins --------
    // The code generator emits a call to the static of the same name for each of these, so this is
    // the single place where their meaning is defined. Equal and Less are IEEE while the operators
    // above are Dafny's; having both under names of their own is what stops one being emitted
    // where the other was meant.
    public static bool Equal(Fp32 a, Fp32 b) => IeeeEqual(a, b);
    public static bool Less(Fp32 a, Fp32 b) => IeeeLess(a, b);
    public static bool LessOrEqual(Fp32 a, Fp32 b) => IeeeLessOrEqual(a, b);
    public static bool Greater(Fp32 a, Fp32 b) => IeeeLess(b, a);
    public static bool GreaterOrEqual(Fp32 a, Fp32 b) => IeeeLessOrEqual(b, a);

    public static Fp32 Add(Fp32 a, Fp32 b) => a + b;
    public static Fp32 Sub(Fp32 a, Fp32 b) => a - b;
    public static Fp32 Mul(Fp32 a, Fp32 b) => a * b;
    public static Fp32 Div(Fp32 a, Fp32 b) => a / b;
    public static Fp32 Neg(Fp32 a) => -a;

    // Each of these computes in double and rounds back. That is exact for Abs, Floor, Ceiling and
    // Round, whose results are already representable in fp32. For Sqrt it is also correctly
    // rounded rather than merely close: double rounding through a format with at least 2p+2 bits
    // is harmless for square root, and 53 >= 2*24+2.
    public static Fp32 Abs(Fp32 a) => new Fp32(Math.Abs(a.value));
    public static Fp32 Floor(Fp32 a) => new Fp32((float)Math.Floor((double)a.value));
    public static Fp32 Ceiling(Fp32 a) => new Fp32((float)Math.Ceiling((double)a.value));
    public static Fp32 Round(Fp32 a) => new Fp32((float)Math.Round((double)a.value, MidpointRounding.ToEven));
    public static Fp32 Sqrt(Fp32 a) => new Fp32((float)Math.Sqrt((double)a.value));
    public static Fp32 FromReal(BigRational r) => new Fp32(r.ToSingle());
    // Narrowing, rounding to nearest. This is the only rounding fp64 -> fp32 conversion, since
    // "as fp32" asserts exact representability instead.
    public static Fp32 FromFp64(Fp64 a) => new Fp32((float)a.Value);

    // SMT-LIB fp.min/fp.max return the other operand when one is NaN instead of propagating it
    // the way Math.Min/Math.Max do, and the verifier relies on that: fp.min(NaN, 1.0) == 1.0 is
    // forced. Their value on the two zeros is left unspecified by SMT-LIB, so either is sound.
    public static Fp32 Min(Fp32 a, Fp32 b) => IsNaN(a) ? b : IsNaN(b) ? a : new Fp32(Math.Min(a.value, b.value));
    public static Fp32 Max(Fp32 a, Fp32 b) => IsNaN(a) ? b : IsNaN(b) ? a : new Fp32(Math.Max(a.value, b.value));

    public static BigInteger ToInt(Fp32 a) => (BigInteger)Math.Truncate((double)a.value);

    public static Fp32 FromInt(BigInteger i) => new Fp32((float)i);
    // Every fp32 value is an fp64 value, so widening first is exact.
    public static BigRational ToReal(Fp32 a) => Fp64.ToReal(Fp64.FromFp32(a));

    public override string ToString() {
      if (float.IsNaN(value)) { return "NaN"; }
      if (float.IsPositiveInfinity(value)) { return "Infinity"; }
      if (float.IsNegativeInfinity(value)) { return "-Infinity"; }
      // Spelled out because .NET Framework's "R" drops the sign on negative zero, and here the
      // sign is the whole difference between two distinct Dafny values.
      if (IsNegativeZero) { return "-0.0"; }
      return FpFormat.DafnyLiteralForm(value.ToString("R", System.Globalization.CultureInfo.InvariantCulture));
    }
  }

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || Count != other.Count) {
        return false;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    BigInteger ElementCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t, out var i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (var t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      // Be sure to use ElementCount to avoid casting into 32 bits
      // integers that could lead to overflows (see https://github.com/dafny-lang/dafny/issues/5554)
      return th.ElementCount < other.ElementCount && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }

      if (t is T && dict.TryGetValue((T)(object)t, out var m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount; }
    }
    public long LongCount {
      get { return (long)ElementCount; }
    }

    public BigInteger ElementCount {
      get {
        // This is inefficient
        var c = occurrencesOfNull;
        foreach (var item in dict) {
          c += item.Value;
        }
        return c;
      }
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || LongCount != other.LongCount) {
        return false;
      }

      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }

      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> : IEnumerable<T> {
    long LongCount { get; }
    int Count { get; }
    [Obsolete("Use CloneAsArray() instead of Elements (both perform a copy).")]
    T[] Elements { get; }
    T[] CloneAsArray();
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
    string ToVerbatimString(bool asLiteral);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var builder = ImmutableArray.CreateBuilder<T>(len);
      for (int i = 0; i < len; i++) {
        builder.Add(init(new BigInteger(i)));
      }
      return new ArraySequence<T>(builder.MoveToImmutable());
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public static ISequence<Rune> UnicodeFromString(string s) {
      var runes = new List<Rune>();

      foreach (var rune in Rune.Enumerate(s)) {
        runes.Add(rune);
      }
      return new ArraySequence<Rune>(runes.ToArray());
    }

    public static ISequence<ISequence<char>> FromMainArguments(string[] args) {
      Dafny.ISequence<char>[] dafnyArgs = new Dafny.ISequence<char>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<char>.FromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<char>.FromString(args[i]);
      }

      return Sequence<ISequence<char>>.FromArray(dafnyArgs);
    }
    public static ISequence<ISequence<Rune>> UnicodeFromMainArguments(string[] args) {
      Dafny.ISequence<Rune>[] dafnyArgs = new Dafny.ISequence<Rune>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<Rune>.UnicodeFromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<Rune>.UnicodeFromString(args[i]);
      }

      return Sequence<ISequence<Rune>>.FromArray(dafnyArgs);
    }

    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = sequence.CloneAsArray();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      for (int i = 0; i < n; i++) {
        if (!Equals(left.Select(i), right.Select(i))) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n <= right.Count && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n < right.Count && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    internal abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements { get { return CloneAsArray(); } }

    public T[] CloneAsArray() {
      return ImmutableElements.ToArray();
    }

    public IEnumerable<T> UniqueElements {
      get {
        return Set<T>.FromCollection(ImmutableElements).Elements;
      }
    }

    public IEnumerator<T> GetEnumerator() {
      foreach (var el in ImmutableElements) {
        yield return el;
      }
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      return ReferenceEquals(this, other) || (Count == other.Count && EqualUntil(this, other, Count));
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (typeof(T) == typeof(char)) {
        return string.Concat(this);
      } else {
        return "[" + string.Join(", ", ImmutableElements.Select(Dafny.Helpers.ToString)) + "]";
      }
    }

    public string ToVerbatimString(bool asLiteral) {
      var builder = new System.Text.StringBuilder();
      if (asLiteral) {
        builder.Append('"');
      }
      foreach (var c in this) {
        var rune = (Rune)(object)c;
        if (asLiteral) {
          builder.Append(Helpers.EscapeCharacter(rune));
        } else {
          builder.Append(char.ConvertFromUtf32(rune.Value));
        }
      }
      if (asLiteral) {
        builder.Append('"');
      }
      return builder.ToString();
    }

    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      return Subsequence(0, m);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      return Subsequence(m, Count);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == Count) {
        return this;
      }
      int startingIndex = checked((int)lo);
      var length = checked((int)hi) - startingIndex;
      return new ArraySequence<T>(ImmutableArray.Create<T>(ImmutableElements, startingIndex, length));
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }

    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    internal volatile ISequence<T> left, right;
    internal ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    internal ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>(count);
      var toVisit = new Stack<ISequence<T>>();
      var leftBuffer = left;
      var rightBuffer = right;
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          leftBuffer = cs.left;
          rightBuffer = cs.right;
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          if (seq is Sequence<T> sq) {
            ansBuilder.AddRange(sq.ImmutableElements); // Optimized path for ImmutableArray
          } else {
            ansBuilder.AddRange(seq); // Slower path using IEnumerable
          }
        }
      }
      return ansBuilder.MoveToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else if (g is Rune) {
        return "'" + EscapeCharacter((Rune)(object)g) + "'";
      } else {
        return g.ToString();
      }
    }

    public static string EscapeCharacter(Rune r) {
      switch (r.Value) {
        case '\n': return "\\n";
        case '\r': return "\\r";
        case '\t': return "\\t";
        case '\0': return "\\0";
        case '\'': return "\\'";
        case '\"': return "\\\"";
        case '\\': return "\\\\";
        default: return r.ToString();
      };
    }

    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<Rune> RUNE = new TypeDescriptor<Rune>(new Rune('D'));  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<Fp32> FP32 = new TypeDescriptor<Fp32>(Fp32.Zero);
    public static readonly TypeDescriptor<Fp64> FP64 = new TypeDescriptor<Fp64>(Fp64.Zero);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x1_0000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<Rune> AllUnicodeChars() {
      for (int i = 0; i < 0xD800; i++) {
        yield return new Rune(i);
      }
      for (int i = 0xE000; i < 0x11_0000; i++) {
        yield return new Rune(i);
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>(array);
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
        // This is unfriendly given that Dafny's C# compiler will
        // invoke the compiled main method directly,
        // so we might be exiting the whole Dafny process here.
        // That's the best we can do until Dafny main methods support
        // a return value though (https://github.com/dafny-lang/dafny/issues/2699).
        // If we just set Environment.ExitCode here, the Dafny CLI
        // will just override that with 0.
        Environment.Exit(1);
      }
    }

    public static Rune AddRunes(Rune left, Rune right) {
      return (Rune)(left.Value + right.Value);
    }

    public static Rune SubtractRunes(Rune left, Rune right) {
      return (Rune)(left.Value - right.Value);
    }

    public static uint Bv32ShiftLeft(uint a, int amount) {
      return 32 <= amount ? 0 : a << amount;
    }
    public static ulong Bv64ShiftLeft(ulong a, int amount) {
      return 64 <= amount ? 0 : a << amount;
    }

    public static uint Bv32ShiftRight(uint a, int amount) {
      return 32 <= amount ? 0 : a >> amount;
    }
    public static ulong Bv64ShiftRight(ulong a, int amount) {
      return 64 <= amount ? 0 : a >> amount;
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    public readonly BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)

    public override string ToString() {
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (DividesAPowerOf10(den, out var factor, out var log10)) {
        var n = num * factor;
        string sign;
        string digits;
        if (n.Sign < 0) {
          sign = "-"; digits = (-n).ToString();
        } else {
          sign = ""; digits = n.ToString();
        }
        if (log10 < digits.Length) {
          var digitCount = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, digitCount), digits.Substring(digitCount));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public static bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    /// <summary>
    /// If this method return true, then
    ///     10^log10 == factor * i
    /// Otherwise, factor and log10 should not be used.
    /// </summary>
    public static bool DividesAPowerOf10(BigInteger i, out BigInteger factor, out int log10) {
      factor = BigInteger.One;
      log10 = 0;
      if (i <= 0) {
        return false;
      }

      BigInteger ten = 10;
      BigInteger five = 5;
      BigInteger two = 2;

      // invariant: 1 <= i && i * 10^log10 == factor * old(i)
      while (i % ten == 0) {
        i /= ten;
        log10++;
      }

      while (i % five == 0) {
        i /= five;
        factor *= two;
        log10++;
      }
      while (i % two == 0) {
        i /= two;
        factor *= five;
        log10++;
      }

      return i == BigInteger.One;
    }

    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(uint n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(long n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(ulong n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    /// <summary>
    /// Construct an exact rational representation of a double value.
    /// Throw an exception on NaN or infinite values. Does not support
    /// subnormal values, though it would be possible to extend it to.
    /// </summary>
    public BigRational(double n) {
      if (Double.IsNaN(n)) {
        throw new ArgumentException("Can't convert NaN to a rational.");
      }
      if (Double.IsInfinity(n)) {
        throw new ArgumentException(
          "Can't convert +/- infinity to a rational.");
      }

      // Double-specific values
      const int exptBias = 1023;
      const ulong signMask = 0x8000_0000_0000_0000;
      const ulong exptMask = 0x7FF0_0000_0000_0000;
      const ulong mantMask = 0x000F_FFFF_FFFF_FFFF;
      const int mantBits = 52;
      ulong bits = BitConverter.ToUInt64(BitConverter.GetBytes(n), 0);

      // Generic conversion
      bool isNeg = (bits & signMask) != 0;
      int expt = ((int)((bits & exptMask) >> mantBits)) - exptBias;
      var mant = (bits & mantMask);

      if (expt == -exptBias && mant != 0) {
        throw new ArgumentException(
          "Can't convert a subnormal value to a rational (yet).");
      }

      var one = BigInteger.One;
      var negFactor = isNeg ? BigInteger.Negate(one) : one;
      var two = new BigInteger(2);
      var exptBI = BigInteger.Pow(two, Math.Abs(expt));
      var twoToMantBits = BigInteger.Pow(two, mantBits);
      var mantNum = negFactor * (twoToMantBits + new BigInteger(mant));
      if (expt == -exptBias && mant == 0) {
        num = den = 0;
      } else if (expt < 0) {
        num = mantNum;
        den = twoToMantBits * exptBI;
      } else {
        num = exptBI * mantNum;
        den = twoToMantBits;
      }
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }

    public bool IsInteger() {
      var floored = new BigRational(this.ToBigInteger(), BigInteger.One);
      return this == floored;
    }

    public static BigRational FromDouble(double n) {
      return new BigRational(n);
    }

    public static BigRational FromFloat(float f) {
      return new BigRational((double)f);
    }

    public double ToDouble() {
      return ToFloatingPointImpl(53, 11);
    }

    public float ToSingle() {
      var result = ToFloatingPointImpl(24, 8);
      return (float)result;
    }

    // Convert rational to IEEE 754 floating-point with RNE
    private double ToFloatingPointImpl(int significandSize, int exponentSize) {
      var bias = (1 << (exponentSize - 1)) - 1;
      var significandFieldBits = significandSize - 1;
      if (num.IsZero) {
        return (den.Sign < 0) ? -0.0 : 0.0;
      }

      var isNegative = num.Sign < 0;
      var absNum = BigInteger.Abs(num);
      var absDen = BigInteger.Abs(den);

      // Scale for precision (extra bits for accurate rounding)
      var numBits = GetBitLength(absNum);
      var denBits = GetBitLength(absDen);
      var scaleBits = significandSize + 3 + Math.Max(0, denBits - numBits);

      var scaledNum = absNum << scaleBits;
      var quotient = BigInteger.DivRem(scaledNum, absDen, out var remainder);

      // Fold the remainder into a sticky bit rather than rounding it away here. The narrowing
      // further down rounds to nearest, ties to even, and rounding twice is not the same as
      // rounding once: the first rounding destroys the residual that decides the second, which
      // lands about one conversion in twenty-five on the neighbouring value.
      //
      // An OR is enough. The scaling above always leaves at least two bits below the narrowing
      // point, so bit 0 is discarded there; and if bit 0 is already set then the discarded tail is
      // already non-zero, so it cannot be the exact tie that the sticky bit exists to break.
      if (!remainder.IsZero) {
        quotient |= BigInteger.One;
      }

      if (quotient.IsZero) {
        return isNegative ? -0.0 : 0.0;
      }
      var quotientBits = GetBitLength(quotient);
      var unbiasedExponent = quotientBits - scaleBits - 1;
      var biasedExponent = unbiasedExponent + bias;
      var maxExponent = (1 << exponentSize) - 1;

      // Handle overflow to infinity
      if (biasedExponent >= maxExponent) {
        return isNegative ? double.NegativeInfinity : double.PositiveInfinity;
      }

      // Handle underflow and subnormals. Far underflow needs no special case: the shift below is
      // computed from the biased exponent, so a value hundreds of binades beneath the smallest
      // subnormal gets a correspondingly large shift and rounds to zero, and a value exactly halfway
      // to the smallest subnormal rounds to even, which is zero. An earlier special case shifted by
      // the quotient's own width instead, which ignores how far below the range the value sits, so
      // 1e-400 came back as the smallest subnormal rather than zero.
      if (biasedExponent <= 0) {
        var shiftAmount = quotientBits - significandSize - biasedExponent + 1;
        if (shiftAmount > 0) {
          quotient = ApplyRoundedRightShift(quotient, shiftAmount);
        }

        if (quotient.IsZero) {
          return isNegative ? -0.0 : 0.0;
        }

        return ConvertSubnormalToDouble(quotient, significandSize, bias, significandFieldBits, isNegative);
      }

      // Normalize significand
      if (quotientBits > significandSize) {
        quotient = ApplyRoundedRightShift(quotient, quotientBits - significandSize);
        if (GetBitLength(quotient) > significandSize) {
          quotient >>= 1;
          biasedExponent++;
          if (biasedExponent >= maxExponent) {
            return isNegative ? double.NegativeInfinity : double.PositiveInfinity;
          }
        }
      }
      var significandField = (ulong)(quotient & ((1L << significandFieldBits) - 1));

      // Convert to 64-bit double format
      const int DOUBLE_SIGNIFICAND_FIELD_BITS = 52;
      const int DOUBLE_EXPONENT_SIZE = 11;
      const int DOUBLE_BIAS = 1023;

      var significandField64 = significandField << (DOUBLE_SIGNIFICAND_FIELD_BITS - significandFieldBits);

      int adjustedExponent;
      var maxExponentValue = (1 << exponentSize) - 1;

      if (biasedExponent == 0) {
        adjustedExponent = 0;
      } else if (biasedExponent == maxExponentValue) {
        adjustedExponent = (1 << DOUBLE_EXPONENT_SIZE) - 1;
      } else {
        var unbias = biasedExponent - bias;
        adjustedExponent = unbias + DOUBLE_BIAS;

        if (adjustedExponent <= 0) {
          adjustedExponent = 0;
        } else if (adjustedExponent >= ((1 << DOUBLE_EXPONENT_SIZE) - 1)) {
          adjustedExponent = (1 << DOUBLE_EXPONENT_SIZE) - 1;
          significandField64 = 0;
        }
      }

      var expBits64 = (ulong)adjustedExponent << DOUBLE_SIGNIFICAND_FIELD_BITS;
      var signBit64 = isNegative ? 0x8000_0000_0000_0000UL : 0;
      var doubleBits = signBit64 | expBits64 | significandField64;
      return BitConverter.Int64BitsToDouble((long)doubleBits);
    }

    // Helper to convert subnormal value from smaller format to double representation
    private static double ConvertSubnormalToDouble(BigInteger quotient, int significandSize, int bias, int significandFieldBits, bool isNegative) {
      if (significandSize < 53) {
        // Calculate actual exponent for this subnormal value
        var actualExponent = 1 - bias - significandFieldBits + GetBitLength(quotient) - 1;
        var doubleExponent = actualExponent + 1023;

        if (doubleExponent > 0) {
          // Smaller format subnormal becomes normal double
          var floatAsDoubleBits = (ulong)doubleExponent << 52;
          if (quotient > 1) {
            var sig = (ulong)((quotient - (BigInteger.One << (GetBitLength(quotient) - 1))) << (52 - (GetBitLength(quotient) - 1)));
            floatAsDoubleBits |= sig;
          }
          if (isNegative) {
            floatAsDoubleBits |= 0x8000_0000_0000_0000UL;
          }

          return BitConverter.Int64BitsToDouble((long)floatAsDoubleBits);
        }
      }
      // Double format subnormal - store directly
      var subnormalBits = (ulong)quotient;
      if (isNegative) {
        subnormalBits |= 0x8000_0000_0000_0000UL;
      }

      return BitConverter.Int64BitsToDouble((long)subnormalBits);
    }

    private static BigInteger ApplyRoundedRightShift(BigInteger value, int shift) {
      if (shift <= 0) {
        return value << -shift;
      }

      var shifted = value >> shift;
      var remainder = value & ((BigInteger.One << shift) - 1);
      var halfPoint = BigInteger.One << (shift - 1);

      if (remainder > halfPoint || (remainder == halfPoint && !shifted.IsEven)) {
        shifted++;
      }

      return shifted;
    }
    private static int GetBitLength(BigInteger value) {
      if (value.IsZero) {
        return 0;
      }

      if (value.Sign < 0) {
        value = -value;
      }

#if NET5_0_OR_GREATER || NET6_0_OR_GREATER
      // Use built-in GetBitLength() method (available in .NET 5.0+)
      // This is O(1) instead of O(n) for n-bit numbers
      return (int)value.GetBitLength();
#else
      // Fallback for older .NET versions - O(n) algorithm
      // Consider using a binary search approach for better performance on large numbers
      var bits = 0;
      var temp = value;
      while (temp > 0) {
        bits++;
        temp >>= 1;
      }
      return bits;
#endif
    }

    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }

      Normalize(this, that, out var aa, out var bb, out var dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}
