// RUN: %exits-with 3 %build --target java "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// C# compiles fp32/fp64; no other backend does yet. Dafny's "==" on these types is value
// identity in the SMT FloatingPoint sort, which keeps +0.0 and -0.0 apart and identifies NaN
// with itself, so |s| below is 2. A backend whose floats are raw IEEE doubles would say 1, and
// for collections it would also hash them wrongly, so compiling this at all is refused until the
// backend has a faithful representation. See Feature.FloatingPointTypes and Dafny.Fp64 in the C#
// runtime for what that takes.
//
// The check is whole-program rather than per-position, so a program that mentions fp only in
// specifications is refused too. Per-position leaks through subset-type witnesses and const
// initialisers.

method CompiledCollection() {
  var s: set<fp64> := {0.0, -0.0};
  assert |s| == 2;
}

// Refused by the same check. The position reported is the start of the program, not any of these
// uses: the check is whole-program, so it has no offending position to point at.
method CompiledScalar(x: fp64) returns (y: fp64) { y := x; }
method CompiledMap() {
  var m: map<fp64, int> := map[0.0 := 1, -0.0 := 2];
}
