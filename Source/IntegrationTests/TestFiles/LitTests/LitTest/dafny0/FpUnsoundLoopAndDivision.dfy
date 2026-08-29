// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Three things that must not be accepted.
//
// The first two share a cause: Boogie's interval inference is unsound for a float assigned in a loop
// whose body branches on it. In Boogie alone the same shape with ordinary values such as 1.0 and 2.0
// also proves a false assertion, while an int or a bool does not -- so this is about neither the
// signed zeros nor decreases. Any fp program is exposed, so the translator turns the analysis off for
// a program that mentions fp at all. The second method has no decreases clause over fp, which locates
// the defect away from the ordering.
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

// A divisor of -0.0 is as much a division by zero as +0.0 is, so the obligation has to test
// fp64_is_zero rather than structural equality against the literal +0.0.
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
