// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This test checks for tricky cases of redundancy suppression when building
// triggers.

ghost predicate P(x: int, y: int)
ghost predicate Q(x: int)
ghost predicate R(x: int)

method M() {
  // For this term, it is enough to order the terms by number of variables
  assert forall x, y :: true || P(x, y) || Q(y) || R(x);
  assert forall x, y :: true || Q(y) || P(x, y) || R(x);
  assert forall x, y :: true || Q(y) || R(x) || P(x, y);
}

ghost predicate PP(x: int, y: int, z: int)
ghost predicate QQ(x: int, y: int)
ghost predicate RR(x: int, y: int)
ghost predicate SS(x: int, y: int)

method MM() {
  // Not for this one, though
  assert forall x, y, z, u, v, w :: true || PP(x, y, z) || QQ(x, u) || RR(y, v) || SS(z, w);
  assert forall x, y, z, u, v, w :: true || QQ(x, u) || PP(x, y, z) || RR(y, v) || SS(z, w);
  assert forall x, y, z, u, v, w :: true || QQ(x, u) || RR(y, v) || PP(x, y, z) || SS(z, w);
  assert forall x, y, z, u, v, w :: true || QQ(x, u) || RR(y, v) || SS(z, w) || PP(x, y, z);
}
