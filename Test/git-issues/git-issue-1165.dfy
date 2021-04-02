// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate method P()

method TestMapMethod(s0: set<int>, s1: set<int>) {
  var m;
  m := map key | key in (s0 + s1) && P() :: true;
  m := map key | key in (s0 + s1) :: true;
  m := map key | key in s0 + s1 && P() :: true;
  m := map key | key in s0 + s1 :: true;
  assert true;
}

function TestMap(s0: set<int>, s1: set<int>): bool {
  // Once, these caused malformed Boogie, because the parentheses had fooled the
  // RewriteInExpr mechanism when generating CanCall assumptions.
  // Ditto for the comprehensions in functions below.
  var m0 := map key | key in (s0 + s1) && P() :: true;
  var m1 := map key | key in (s0 + s1) :: true;
  var m2 := map key | key in s0 + s1 && P() :: true;
  var m3 := map key | key in s0 + s1 :: true;
  true
}

function TestSet(s0: set<int>, s1: set<int>): bool {
  var t0 := set key | key in (s0 + s1) && P() :: key;
  var t1 := set key | key in (s0 + s1) :: key;
  var t2 := set key | key in s0 + s1 && P() :: key;
  var t3 := set key | key in s0 + s1 :: key;
  true
}

function TestInMultiset(s0: multiset<int>, s1: multiset<int>): bool {
  var t0 := set key | key in (s0 + s1) && P() :: key;
  var t1 := set key | key in (s0 + s1) :: key;
  var t2 := set key | key in s0 + s1 && P() :: key;
  var t3 := set key | key in s0 + s1 :: key;
  true
}
