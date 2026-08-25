// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Three things that were accepted and should not be.
//
// The first two share a cause: Boogie's interval inference is unsound for a float assigned in a loop
// whose body branches on it. Reduced to Boogie alone, the same shape with ordinary values such as 1.0
// and 2.0 also proves a false assertion, while an int or a bool in that shape does not -- so this is
// not about the signed zeros, and not about decreases. Any fp program is exposed, so the translator
// turns the analysis off for a program that mentions fp at all.
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

// The same defect without a decreases clause over fp: termination is by an int counter, and the fp
// local is only assigned in a loop that branches on it. The iteration count is ODD, so on exit m is
// -0.0 and the assertion is false. The count matters -- with an even count the assertion is TRUE and
// the test would pin the solver's incompleteness rather than its soundness.
method FalseAssertionUnderIntervalInference() {
  var m: fp64 := 0.0;
  var i := 0;
  while i < 11
    decreases 11 - i
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
