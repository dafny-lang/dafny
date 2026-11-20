// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

// Every member of fp32 and fp64 that can appear in compiled code, used once.
//
// The C# translation of each is a static of the same name on Dafny.Fp32/Dafny.Fp64, so a member with
// no runtime counterpart produces generated code that does not compile. Naming them all here turns
// that into a test failure rather than something a user discovers.
//
// Where the verifier can pin the answer, it does, so the compiled result is checked against the
// specification rather than against a recording of itself.

method Classification() {
  var x: fp64 := 1.5;
  var nan := fp64.NaN;
  var inf := fp64.PositiveInfinity;
  var negZero: fp64 := -0.0;

  assert x.IsNormal && !x.IsNaN && x.IsFinite && x.IsPositive;
  // NaN has no sign, which is where System.Double disagrees: its NaN has the sign bit set.
  assert !nan.IsNegative && !nan.IsPositive;
  assert negZero.IsZero && negZero.IsNegative;
  assert fp64.MinSubnormal.IsSubnormal;
  assert inf.IsInfinite && !inf.IsFinite;

  print "IsNaN: ", x.IsNaN, " ", nan.IsNaN, "\n";
  print "IsFinite: ", x.IsFinite, " ", inf.IsFinite, "\n";
  print "IsInfinite: ", x.IsInfinite, " ", inf.IsInfinite, "\n";
  print "IsNormal: ", x.IsNormal, " ", fp64.MinSubnormal.IsNormal, "\n";
  print "IsSubnormal: ", x.IsSubnormal, " ", fp64.MinSubnormal.IsSubnormal, "\n";
  print "IsZero: ", x.IsZero, " ", negZero.IsZero, "\n";
  print "IsNegative: ", negZero.IsNegative, " ", nan.IsNegative, "\n";
  print "IsPositive: ", x.IsPositive, " ", nan.IsPositive, "\n";
}

method Constants() {
  assert fp64.NaN.IsNaN;
  assert fp64.PositiveInfinity.IsInfinite && fp64.NegativeInfinity.IsNegative;
  assert fp64.MaxValue.IsNormal && fp64.MinValue.IsNegative;
  assert fp64.MinNormal.IsNormal && fp64.MinSubnormal.IsSubnormal;
  assert !fp64.Pi.IsNaN && !fp64.E.IsNaN && !fp64.Epsilon.IsNaN;

  print "NaN: ", fp64.NaN, "\n";
  print "infinities: ", fp64.PositiveInfinity, " ", fp64.NegativeInfinity, "\n";
  print "Pi: ", fp64.Pi, "\n";
  print "E: ", fp64.E, "\n";
  print "MaxValue: ", fp64.MaxValue, "\n";
  print "MinValue: ", fp64.MinValue, "\n";
  print "MinNormal: ", fp64.MinNormal, "\n";
  print "MinSubnormal: ", fp64.MinSubnormal, "\n";
  print "Epsilon: ", fp64.Epsilon, "\n";
  print "fp32 Pi and E: ", fp32.Pi, " ", fp32.E, "\n";
}

// The static family: IEEE, and so obligation-free. The comparisons here differ from < and <= in
// their answers, not only in their preconditions, which is why they have names of their own.
method IeeeOperations() {
  var a: fp64 := 1.5;
  var b: fp64 := 2.5;
  var negZero: fp64 := -0.0;
  var posZero: fp64 := 0.0;

  assert fp64.Add(a, b) == 4.0;
  assert fp64.Sub(b, a) == 1.0;
  assert fp64.Mul(a, b) == 3.75;
  assert fp64.Div(b, a) == fp64.Div(b, a);
  assert fp64.Neg(posZero) == negZero;
  // IEEE, so the two zeros are equal here and neither is below the other.
  assert fp64.Equal(negZero, posZero);
  assert !fp64.Less(negZero, posZero);
  assert fp64.LessOrEqual(negZero, posZero);

  print "Add/Sub/Mul/Div: ", fp64.Add(a, b), " ", fp64.Sub(b, a), " ",
        fp64.Mul(a, b), " ", fp64.Div(b, a), "\n";
  print "Neg: ", fp64.Neg(a), "\n";
  print "Equal(-0.0, 0.0): ", fp64.Equal(negZero, posZero), "\n";
  print "Less/LessOrEqual: ", fp64.Less(a, b), " ", fp64.LessOrEqual(a, b), "\n";
  print "Greater/GreaterOrEqual: ", fp64.Greater(a, b), " ", fp64.GreaterOrEqual(a, b), "\n";
  print "Less(-0.0, 0.0) is IEEE: ", fp64.Less(negZero, posZero), "\n";
}

// Dafny's order is total, with NaN above every number, so a comparison against NaN is answered rather
// than refused. This is where the compiled answer is furthest from the platform's: in C# every
// comparison against double.NaN is false, so the first four lines would be wrong if Dafny.Fp64
// delegated to double. Each claim is asserted before it is printed.
method TotalOrderIncludingNaN() {
  var one: fp64 := 1.0;
  var nan := fp64.NaN;
  var inf := fp64.PositiveInfinity;
  var f: fp32 := 1.0;

  assert one < nan;
  assert inf < nan;              // above the infinities, not merely above the finite values
  assert !(nan < one);
  assert one <= nan;
  assert !(nan <= one);
  assert nan > one && nan >= one;
  assert !(nan < nan);           // strict
  assert nan <= nan;             // but reflexive, because "==" is
  assert f < fp32.NaN;
  // The IEEE family is unchanged: false in both directions, which is what C# would give for all of
  // the above.
  assert !fp64.Less(one, nan) && !fp64.Less(nan, one);
  assert !fp64.LessOrEqual(one, nan) && !fp64.LessOrEqual(nan, nan);

  print "1.0 < NaN: ", one < nan, "\n";
  print "inf < NaN: ", inf < nan, "\n";
  print "NaN < 1.0: ", nan < one, "\n";
  print "1.0 <= NaN: ", one <= nan, " NaN <= 1.0: ", nan <= one, "\n";
  print "NaN > 1.0: ", nan > one, " NaN >= 1.0: ", nan >= one, "\n";
  print "NaN < NaN: ", nan < nan, " NaN <= NaN: ", nan <= nan, "\n";
  print "fp32 1.0 < NaN: ", f < fp32.NaN, "\n";
  print "IEEE Less(1.0, NaN): ", fp64.Less(one, nan), " Less(NaN, 1.0): ", fp64.Less(nan, one), "\n";
}

method MathematicalFunctions() {
  var x: fp64 := 1.5;
  var nine: fp64 := 9.0;

  assert fp64.Abs(-x) == 1.5 && fp64.Abs(x) == 1.5;
  assert fp64.Floor(x) == 1.0 && fp64.Ceiling(x) == 2.0;
  assert fp64.Round(2.5) == 2.0 && fp64.Round(3.5) == 4.0;   // ties to even
  assert fp64.Sqrt(nine) == 3.0;
  assert fp64.Min(x, nine) == x && fp64.Max(x, nine) == nine;
  assert fp32.Sqrt(9.0) == 3.0;

  print "Abs: ", fp64.Abs(-x), " ", fp64.Abs(x), "\n";
  print "Floor/Ceiling: ", fp64.Floor(x), " ", fp64.Ceiling(x), "\n";
  print "Round ties to even: ", fp64.Round(2.5), " ", fp64.Round(3.5), "\n";
  print "Sqrt: ", fp64.Sqrt(nine), "\n";
  print "Min/Max: ", fp64.Min(x, nine), " ", fp64.Max(x, nine), "\n";
  print "fp32 Sqrt: ", fp32.Sqrt(9.0), "\n";
}

// The fp64.* family on the arguments where IEEE has no numeric result. Reachable only because the
// family carries no obligations, so the compiled behaviour here needs pinning: every line is asserted
// before it is printed.
method IeeeFamilyOnNonNumericArguments() {
  var nan := fp64.NaN;
  var negZero: fp64 := -0.0;

  assert fp64.Sqrt(-1.0).IsNaN;          // IEEE: a negative gives NaN
  assert fp64.Sqrt(negZero) == negZero;  // but -0.0 gives -0.0, despite fp.isNegative(-0.0)
  assert fp64.Sqrt(nan).IsNaN;
  assert fp64.Abs(nan).IsNaN;
  assert fp64.Floor(nan).IsNaN && fp64.Ceiling(nan).IsNaN && fp64.Round(nan).IsNaN;
  assert fp64.Min(nan, 1.0) == 1.0;      // IEEE discards a NaN rather than propagating it
  assert fp64.Max(nan, 1.0) == 1.0;
  assert fp32.Sqrt(-1.0).IsNaN;

  print "Sqrt(-1.0): ", fp64.Sqrt(-1.0), "   Sqrt(-0.0): ", fp64.Sqrt(negZero), "\n";
  print "Sqrt(NaN): ", fp64.Sqrt(nan), "   Abs(NaN): ", fp64.Abs(nan), "\n";
  print "Floor/Ceiling/Round(NaN): ", fp64.Floor(nan), " ", fp64.Ceiling(nan), " ", fp64.Round(nan), "\n";
  print "Min(NaN, 1.0): ", fp64.Min(nan, 1.0), "   Max(NaN, 1.0): ", fp64.Max(nan, 1.0), "\n";
  print "fp32 Sqrt(-1.0): ", fp32.Sqrt(-1.0), "\n";
}

// The conversions whose value the verifier can pin. These are separated from the method below
// because "as int" and "as real" go through fp.to_real, which is expensive enough that sharing a
// proof context with them pushes the whole method past its time limit.
method ConversionsWithProvableValues() {
  var f: fp32 := 4.0;

  assert f as fp64 == 4.0;            // widening: exact
  assert 3 as fp64 == 3.0;            // int to fp
  assert fp32.FromFp64(1.5) == 1.5;   // exactly representable, so the narrowing is exact

  // Deliberately absent: no assertion about a real-to-fp conversion's VALUE. Neither
  // "1.5 as fp64 == 1.5" nor "fp64.FromReal(1.5) == 1.5" verifies, at either width. The conversion
  // is modelled as SMT-LIB's (_ to_fp) with RNE, and the solver will not evaluate that on a
  // constant, so the result is opaque even when the source is a literal. The other three directions
  // above are fine, which locates the gap precisely.
  print "conversions with provable values: ok\n";
}

method Conversions() {
  var x: fp64 := 2.0;
  var f: fp32 := 4.0;

  print "fp64 as int: ", (x as int) + 0, "\n";
  print "fp32 as int: ", (f as int) + 0, "\n";
  print "fp32 as fp64: ", f as fp64, "\n";
  print "int as fp64: ", 3 as fp64, "\n";
  print "fp64 as real: ", x as real, "\n";
  print "real as fp64: ", 1.5 as fp64, "\n";
  print "FromReal: ", fp64.FromReal(1.5), " ", fp32.FromReal(1.5), "\n";
  print "ToInt truncates: ", fp64.ToInt(~1.7), " ", fp64.ToInt(~-1.7), "\n";
  print "fp32.FromFp64 rounds: ", fp32.FromFp64(~1e-1), "\n";
}

method Main() {
  Classification();
  Constants();
  IeeeOperations();
  TotalOrderIncludingNaN();
  MathematicalFunctions();
  IeeeFamilyOnNonNumericArguments();
  ConversionsWithProvableValues();
  Conversions();
}
