// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate method P()

method TestMapMethod(s0: set<int>, s1: set<int>) {
  var m;
  m := map key | key in (s0 + s1) && P() :: true; // warning: no trigger
  m := map key | key in (s0 + s1) :: true; // warning: no trigger
  m := map key | key in s0 + s1 && P() :: true; // warning: no trigger
  m := map key | key in s0 + s1 :: true; // warning: no trigger
  assert true;
}

function TestMap(s0: set<int>, s1: set<int>): bool {
  // Once, these caused malformed Boogie, because the parentheses had fooled the
  // RewriteInExpr mechanism when generating CanCall assumptions.
  // Ditto for the comprehensions in functions below.
  var m0 := map key | key in (s0 + s1) && P() :: true; // warning: no trigger
  var m1 := map key | key in (s0 + s1) :: true; // warning: no trigger
  var m2 := map key | key in s0 + s1 && P() :: true; // warning: no trigger
  var m3 := map key | key in s0 + s1 :: true; // warning: no trigger
  true
}

function TestSet(s0: set<int>, s1: set<int>): bool {
  var t0 := set key | key in (s0 + s1) && P() :: key; // warning: no trigger
  var t1 := set key | key in (s0 + s1) :: key; // warning: no trigger
  var t2 := set key | key in s0 + s1 && P() :: key; // warning: no trigger
  var t3 := set key | key in s0 + s1 :: key; // warning: no trigger
  true
}

function TestInMultiset(s0: multiset<int>, s1: multiset<int>): bool {
  var t0 := set key | key in (s0 + s1) && P() :: key; // warning: no trigger
  var t1 := set key | key in (s0 + s1) :: key; // warning: no trigger
  var t2 := set key | key in s0 + s1 && P() :: key; // warning: no trigger
  var t3 := set key | key in s0 + s1 :: key; // warning: no trigger
  true
}
