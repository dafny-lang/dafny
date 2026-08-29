// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Deliberately not %testDafnyForEachResolver, which the other fp tests use: the legacy resolver
// emits NONE of the arithmetic well-formedness obligations below for a newtype over fp, because it
// does not inherit fp64's members into the newtype in the first place. Running both resolvers here
// would mean keeping a second golden file that records that gap as though it were intended.

// Dafny's fp type tests (IsFp32Type / IsFp64Type / IsFloatingPointType) are defined via
// NormalizeExpand(), which sees through type synonyms and subset types but NOT newtypes, while
// IsNumericBased(Float) and NormalizeToAncestorType() do see through newtypes. Any site that asks
// a representation question through an unnormalized test silently skips every fp obligation for a
// newtype, which makes a falsehood provable:
//
//   newtype MyF = fp64
//   lemma Bad(x: MyF) requires (x as fp64).IsInfinite { assert (x as real) == 0.0; }
//
// "as real" translates to "if isFinite then to_real(x) else 0.0", so a skipped finiteness obligation
// leaves the else branch reachable and pins the value to 0.0.
//
// This file pins OBLIGATION PARITY: every spelling of "a floating-point type" must produce the
// same well-formedness errors. Each method below should report the same obligations as Plain.

type Syn = fp64
type Sub = x: fp64 | true
newtype New = fp64
newtype New32 = fp32
type SynOfNew = New

method Plain(x: fp64, y: fp64) {
  var m := -x;
  var a := x + y;
  var b := x - y;
  var c := x * y;
  var d := x < y;
}

method ViaSynonym(x: Syn, y: Syn) {
  var m := -x;
  var a := x + y;
  var b := x - y;
  var c := x * y;
  var d := x < y;
}

method ViaSubsetType(x: Sub, y: Sub) {
  var m := -x;
  var a := x + y;
  var b := x - y;
  var c := x * y;
  var d := x < y;
}

method ViaNewtype(x: New, y: New) {
  var m := -x;
  var a := x + y;
  var b := x - y;
  var c := x * y;
  var d := x < y;
}

method ViaSynonymOfNewtype(x: SynOfNew, y: SynOfNew) {
  var m := -x;
  var a := x + y;
  var b := x - y;
  var c := x * y;
  var d := x < y;
}

// A newtype over fp32 must select the fp32 builtins; an unnormalized prefix gives fp64_is_infinite
// applied to a float24e8, which is ill-typed Boogie.
method Fp32Newtype(x: New32, y: New32) {
  var a := x + y;
}

// Conversions out of a newtype need their obligations too.
method Conversions(x: New) {
  var r := x as real;
  var i := x as int;
}

// The falsehood itself, unprovable while the finiteness obligation is emitted.
lemma InfiniteIsNotZero(x: New)
  requires (x as fp64).IsInfinite
{
  assert (x as real) == 0.0;
}

// A synthesized fp zero must carry ResolvedFloatValue, or the translator asserts. Both shapes below
// ask for one via Zero(): a witness-less subset type needs a default, assign-such-that a start.
type NonNaN = x: fp64 | !x.IsNaN
type NonNaN32 = x: fp32 | !x.IsNaN
type OverNewtype = x: New | true

method WitnessLessSubsetTypes(a: NonNaN, b: NonNaN32, c: OverNewtype) {
  var x := a;
  var y := b;
  var z := c;
}

method AssignSuchThat(v: fp64) {
  var e: fp64 :| e == v;
}
