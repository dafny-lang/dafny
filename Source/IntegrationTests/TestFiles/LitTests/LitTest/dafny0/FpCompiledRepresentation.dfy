// RUN: %testDafnyForEachResolver "%s"
// NONUNIFORM: C# is the only backend that compiles floating point
// RUN: %run --no-verify --target cs "%s" > "%t"
// RUN: %diff "%s.expect_run" "%t"

// Floating point reached through something other than a bare fp32/fp64 type: a newtype, a subset
// type, an array element, a field, a collection element. Each of these asks a different part of
// the pipeline "what is this type, really", and getting fp wrong in any of them used to produce
// either a Boogie type error or invalid C#.
//
// A newtype over fp32 is the interesting case, because "is this an fp32" and "what does this
// compile to" have different answers for it. Asking the first where the second was meant made
// literals fall through to the "real" translation, which the verifier rejected with "cannot assign
// real to float24e8" and the C# compiler rejected with "cannot convert BigRational to Fp32".

newtype MyFloat = fp32
type NonNaN = x: fp64 | !x.IsNaN witness 0.0

class Holder {
  var value: fp64
  constructor(v: fp64) {
    value := v;
  }
}

method NewtypeLiterals() {
  var m: MyFloat := 1.5;
  var neg: MyFloat := -0.0;
  var pos: MyFloat := 0.0;

  assert neg != pos;
  // Via an explicit conversion, because the legacy resolver does not inherit fp32's members into
  // a newtype over it. That is a resolver difference of its own, not part of what is tested here.
  assert (neg as fp32).IsNegative && (neg as fp32).IsZero;
  print "newtype 1.5: ", m, "\n";
  print "newtype -0.0 == 0.0: ", neg == pos, "\n";
  print "newtype -0.0 < 0.0: ", neg < pos, "\n";
  print "newtype -0.0 is negative: ", (neg as fp32).IsNegative, "\n";
}

method NewtypeArithmetic() {
  var m: MyFloat := 1.5;
  print "newtype 1.5 + 1.5: ", m + m, "\n";
  print "newtype 1.5 * 1.5: ", m * m, "\n";
  print "newtype -(1.5): ", -m, "\n";
}

method NewtypeCollections() {
  var s: set<MyFloat> := {0.0, -0.0};
  assert |s| == 2;
  print "|newtype {+0.0, -0.0}|: ", |s|, "\n";
}

method SubsetTypes() {
  var x: NonNaN := 1.5;
  print "subset type 1.5: ", x, "\n";
}

// The all-zero bit pattern has to be the Dafny default, which is +0.0 rather than -0.0.
method Arrays() {
  var a := new fp64[3];
  print "array defaults: ", a[0], " ", a[1], "\n";
  print "array default is positive zero: ", a[0].IsZero && !a[0].IsNegative, "\n";
  a[0] := -0.0;
  print "a[0] == a[1] after storing -0.0: ", a[0] == a[1], "\n";
}

method Fields() {
  var h := new Holder(-0.0);
  print "field is negative zero: ", h.value.IsZero && h.value.IsNegative, "\n";
  h.value := fp64.NaN;
  print "field is NaN: ", h.value.IsNaN, "\n";
}

// Printing has to keep the sign of a zero, since that is the whole difference between two values.
method Printing() {
  var q: seq<fp64> := [1.0, -0.0, 0.0, fp64.NaN, fp64.PositiveInfinity];
  print "seq: ", q, "\n";
  var s: set<fp64> := {1.0};
  print "set: ", s, "\n";
  var m: map<fp64, fp64> := map[1.0 := -0.0];
  print "map: ", m, "\n";
}

method Main() {
  NewtypeLiterals();
  NewtypeArithmetic();
  NewtypeCollections();
  SubsetTypes();
  Arrays();
  Fields();
  Printing();
}
