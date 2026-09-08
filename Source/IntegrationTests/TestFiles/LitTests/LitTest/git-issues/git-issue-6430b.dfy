// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Companion to git-issue-6430.dfy. That test exercises only the direct-call frame
// axiom (BoogieGenerator.Functions.cs). The assertions below reach the SAME
// unsoundness through the arrow-type/handle frame axioms
// (BoogieGenerator.Types.cs, AddArrowTypeAxioms), which the other test does not
// cover: reverting the Types.cs half of the fix leaves that test passing.
//
// Each method carries `ensures false` rather than a trailing `assert x == y`. A
// failing assertion is assumed from then on, so an error on it does not show that
// `false` became unprovable; an unprovable `ensures false` does.

class C {
  var v: int
}

function F(c: C, a: int, b: int): int
  reads *
{
  if c.v == 101 then a else b
}

predicate P(c: C)
  reads *
{
  c.v == 101
}

// Merely mentioning F naked brings the arrow-type axioms into play.
method NakedInScope(a: int, b: int)
  requires a != b
  ensures false // error: reads * must not be framed across the heap change below
{
  var g := F;
  var c := new C;
  c.v := 101;
  var x := F(c, a, b);
  assert x == a;
  c.v := 102;
  var y := F(c, a, b);
  assert y == b;
}

// Applying the function through a handle.
method ThroughHandle(a: int, b: int)
  requires a != b
  ensures false // error
{
  var g := F;
  var c := new C;
  c.v := 101;
  var x := g(c, a, b);
  assert x == a;
  c.v := 102;
  var y := g(c, a, b);
  assert y == b;
}

// A lambda with `reads *` that reads the field directly.
method Lambda(a: int, b: int)
  requires a != b
  ensures false // error
{
  var h := (cc: C) reads * => if cc.v == 101 then a else b;
  var c := new C;
  c.v := 101;
  var x := h(c);
  assert x == a;
  c.v := 102;
  var y := h(c);
  assert y == b;
}

// A handle stored in a collection.
method HandleInSeq(a: int, b: int)
  requires a != b
  ensures false // error
{
  var s := [F];
  var c := new C;
  c.v := 101;
  var x := s[0](c, a, b);
  assert x == a;
  c.v := 102;
  var y := s[0](c, a, b);
  assert y == b;
}

// A `reads *` predicate, whose value must also not be framed across a heap change.
method Predicate()
  ensures false // error
{
  var c := new C;
  c.v := 101;
  var p1 := P(c);
  assert p1;
  c.v := 102;
  var p2 := P(c);
  assert !p2;
}
