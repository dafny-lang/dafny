// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Two things that were accepted and should not be.
//
// The loop below alternates its metric between -0.0 and +0.0. Under Dafny's order those are two
// values with -0.0 below +0.0, so the metric does not decrease every iteration and the loop does not
// terminate -- yet it verified, which let "ensures false" through and a caller prove anything.
// Boogie's interval domain was the cause: it compares floats numerically, so it saw the two zeros as
// one point and narrowed the free invariant that a decreases clause emits, hiding the alternation.
// The translator now turns that analysis off for any program mentioning fp.
method Diverge() returns (r: int)
  ensures false
{
  var m: fp64 := 0.0;
  r := 0;
  while true
    decreases m
  {
    m := if m == 0.0 then -0.0 else 0.0;
  }
}

// A divisor of -0.0 is as much a division by zero as +0.0 is. The obligation used to compare the
// divisor against the literal +0.0, and equality on floats is structural, so -0.0 satisfied it.
method DivideByNegativeZero(x: fp64) returns (r: fp64)
  requires !x.IsNaN
{
  var negZero: fp64 := -0.0;
  r := x / negZero;
}

method DivideByPositiveZero(x: fp64) returns (r: fp64)
  requires !x.IsNaN
{
  var posZero: fp64 := 0.0;
  r := x / posZero;
}
