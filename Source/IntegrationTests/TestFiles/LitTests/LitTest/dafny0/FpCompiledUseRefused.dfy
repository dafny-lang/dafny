// RUN: %exits-with 3 %build --target cs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// fp32/fp64 are verification-only. Their Boogie encoding is equality on the SMT
// FloatingPoint sort, which keeps +0.0 and -0.0 apart and identifies NaN with itself;
// no backend's runtime reproduces that, and for collections the verifier never guards
// element equality or hashing at all. So the verifier proves |s| == 2 below while .NET
// would give 1. Compiling any of this is refused; see Feature.FloatingPointTypes.
// The check is whole-program rather than per-position, so a program that mentions fp only in
// specifications is refused too. An earlier per-position version leaked twice -- on subset-type
// witnesses and on const initialisers -- and fp is verification-only either way.

method CompiledCollection() {
  var s: set<fp64> := {0.0, -0.0};
  assert |s| == 2;
}

// Refused by the same check, though only the first offending use is reported:
method CompiledScalar(x: fp64) returns (y: fp64) { y := x; }
method CompiledMap() {
  var m: map<fp64, int> := map[0.0 := 1, -0.0 := 2];
}
