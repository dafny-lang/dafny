// RUN: %testDafnyForEachResolver "%s"
// NONUNIFORM: C# is the only backend that compiles floating point
// RUN: %run --no-verify --target cs "%s" > "%t"
// RUN: %diff "%s.expect_run" "%t"

// Every member of fp32 and fp64 that can appear in compiled code, used once.
//
// The C# translation of each of these is a static of the same name on Dafny.Fp32/Dafny.Fp64, so a
// member without a runtime counterpart produces generated code that does not compile. Naming them
// all here turns that into a test failure rather than something a user discovers. Ten of the
// unchecked methods were missing exactly that way, and IsNegative and IsZero were present but
// wrong.
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

// The unchecked family: the operators without their well-formedness obligations. The comparisons
// here are IEEE, unlike < and <=, which is why they have names of their own.
method UncheckedOperations() {
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

method MathematicalFunctions() {
  var x: fp64 := 1.5;
  var nine: fp64 := 9.0;

  print "Abs: ", fp64.Abs(-x), " ", fp64.Abs(x), "\n";
  print "Floor/Ceiling: ", fp64.Floor(x), " ", fp64.Ceiling(x), "\n";
  print "Round ties to even: ", fp64.Round(2.5), " ", fp64.Round(3.5), "\n";
  print "Sqrt: ", fp64.Sqrt(nine), "\n";
  print "Min/Max: ", fp64.Min(x, nine), " ", fp64.Max(x, nine), "\n";
  print "fp32 Sqrt: ", fp32.Sqrt(9.0), "\n";
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
  UncheckedOperations();
  MathematicalFunctions();
  Conversions();
}
