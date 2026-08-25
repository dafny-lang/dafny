// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Three things that were accepted and should not be.
//
// The first two share a cause: Boogie's interval abstract domain is unsound for floating point. It
// compares floats numerically, so it treats -0.0 and +0.0 as one point, and the invariant it infers
// is then used as Boogie's equality on floats, which is structural and tells them apart. Any fp
// program is exposed, not just one with a decreases clause, so the translator turns the analysis off
// for a program that mentions fp at all.
//
// This is not specific to this feature's ordering refinement, and predates it: the second method
// below has no decreases clause over fp and proved a false assertion. What the refinement changed is
// that an fp metric used to crash translation, so the first method could not be written at all.
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

// The mechanism, isolated: termination here is by an int counter, and the only fp involvement is a
// local that alternates between the two zeros. The assertion is false, because m may be -0.0, and
// the interval domain proved it.
method FalseAssertionFromIntervalNarrowing() {
  var m: fp64 := 0.0;
  var i := 0;
  while i < 10
    decreases 10 - i
  {
    m := if m == 0.0 then -0.0 else 0.0;
    i := i + 1;
  }
  assert m == 0.0;
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
