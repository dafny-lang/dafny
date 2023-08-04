// RUN: %exits-with 4 %dafny /compile:0 /dprint:"%t.dprint.dfy" "%s" > "%t"
// RUN: %dafny /noVerify "%t.dprint.dfy" >> "%t"
// RUN: %diff "%s.expect" "%t"

// For a body-less loop specification, a local variable or
// out-parameter "x" is havocked by the loop translation
// if "x" is mentioned in the loop guard, loop invariant,
// or loop decreases clause (but what's in the loop's modifies
// clause does not matter).
// A heap location "o.f" is havocked by the loop translation
// if
//   - the heap location is mutable (that is, not a const field)
//   - the heap is mentioned in the loop guard, loop
//     invariant, or loop decreases clause, or the loop bears
//     a modifies clause, AND
//   - "o.f" would be allowed to be modified in the loop body
//     (because "o.f" is newly allocated in the method body,
//     or the loop bears a modifies clause that allows
//     "o.f", or the loop bears no modifies clause but the
//     method's modifies clause allows "o.f".

// Local variables and out-parameters

method L0(n: nat) {
  var i, j := 0, 2;
  while i < n  // targets: i
    invariant 0 <= i <= n
  assert i == n;
  assert j == 2;
  assert n == 0;  // error: should not be provable
}

method L1(n: nat) returns (i: int, j: int) {
  i, j := 0, 2;
  while i < n  // targets: i
    invariant 0 <= i <= n
  assert i == n;
  assert j == 2;
  assert n == 0;  // error: should not be provable
}

method L2(n: int) returns (r: int, s: int)
{
  r := s;
  var i := 0;
  while i < n  // targets: i
  assert r == s;
  assert i == 0;  // error: should not be provable, since i is in guard
}

method L3(n: int) returns (r: int, s: int)
{
  var kn, kr, ks := n, r, s;
  var i := 0;
  while i < n + s  // targets: i, s
  assert kn == n;  // of course, since n never changes
  assert i == 0;  // error: should not be provable, since i is in guard
  assert kr == r;
  assert ks == s;  // error: should not be provable, since s is in guard
}

method L4(a: array<int>, n: int) returns (r: int, s: int)
  modifies a
{
  var ks := s;
  r := n;
  var i := 0;
  while i < n + s  // targets: i, s, $Heap
    modifies if r < 3 then {a} else {}
  assert i == 0;  // error: should not be provable, since i is in guard
  assert r == n;  // yes, because the mention of r just in the modifies clause doesn't count
  assert s == ks;  // error: should not be provable, since s is in guard
}

method L5(a: array<int>, n: int) returns (r: int, s: int)
{
  var ks := s;
  r := n;
  var i := 0;
  while i < n + s  // targets: i, s, r
    decreases r
  assert r == n;  // error: since r was mentioned in the decreases clause
  assert s == ks;  // error: should not be provable, since s is in guard
}

method L6() {
  var i, j := 0, 2;
  while false  // no targets
  assert i == 0;
  assert j == 0;  // error: j is 2
}

// Heap

class C {
  var y: int
  var m: nat
  const u: int
}

method M0(a: array<int>, n: nat)
  requires a.Length == 10
  modifies a
{
  var i := 0;
  while i < n  // targets: i
    invariant 0 <= i <= n
  assert i == n;
  assert a[0] == old(a[0]);  // provable, because heap is not mentioned in loop spec
  assert n == 0;  // error: should not be provable
}

method M1(a: array<int>, b: array<int>, n: nat)
  requires a != b && a.Length == 10
  modifies a
{
  var i := 0;
  while i < n  // targets: i
    invariant 0 <= i <= n && a != b
  assert i == n;
  assert a[0] == old(a[0]);  // provable, because heap is not mentioned in loop spec
  assert n == 0;  // error: should not be provable
}

method M2(a: array<int>, b: array<int>, n: nat)
  requires a != b && 10 <= a.Length == b.Length
  modifies a
{
  var i := 0;
  while i < n  // targets: i, $Heap
    invariant 0 <= i <= n && a != b
    invariant a[0] == old(a[0])
  assert i == n;
  assert a[0] == old(a[0]);  // follows from invariant
  assert b[1] == old(b[1]);  // b is not in any modifies clause
  assert a[1] == old(a[1]);  // error: should not be provable
  assert n == 0;  // error: should not be provable
}

method M3(a: array<int>, b: array<int>, n: nat)
  requires a != b && 10 <= a.Length == b.Length
  modifies a
{
  var i := 0;
  while i < n  // targets: i, $Heap
    invariant 0 <= i <= n && a != b
    invariant b[0] == old(b[0])  // redundant, but this mentions the heap
  assert i == n;
  assert a[0] == old(a[0]);  // error: should not be provable
  assert b[1] == old(b[1]);  // b is not in any modifies clause
  assert n == 0;  // error: should not be provable
}

method M4(a: array<int>, b: array<int>, n: nat)
  requires a != b && 10 <= a.Length == b.Length
  modifies a, b
{
  var i := 0;
  while i < n  // targets: i, $Heap
    invariant 0 <= i <= n && a != b
    invariant a[0] == old(a[0])
  assert i == n;
  assert a[0] == old(a[0]);
  assert b[1] == old(b[1]);  // error: should not be provable
  assert a[1] == old(a[1]);  // error: should not be provable
}

method M5(a: array<int>, b: array<int>, n: nat)
  requires a != b && 10 <= a.Length == b.Length
  modifies a, b
{
  var i := 0;
  while i < n  // targets: i, $Heap
    invariant 0 <= i <= n && a != b
    invariant a[0] == old(a[0])
    modifies a
  assert i == n;
  assert a[0] == old(a[0]);  // fine, because of invariant
  assert b[1] == old(b[1]);  // fine, because loop says "modifies a"
  assert a[1] == old(a[1]);  // error: should not be provable
  assert n == 0;  // error: should not be provable
}

method M6(a: array<int>, b: array<int>, n: nat)
  requires a != b && 10 <= a.Length == b.Length
  modifies a, b
{
  var i := 0;
  while i < n  // targets: i, $Heap
    invariant 0 <= i <= n && a != b
    modifies a
  assert i == n;
  assert a[0] == old(a[0]);  // error: should not be provable
  assert b[1] == old(b[1]);  // fine, because loop says "modifies a"
  assert a[1] == old(a[1]);  // error: should not be provable
  assert n == 0;  // error: should not be provable
}

method M7(c: C, n: nat)
  modifies c
{
  var i := 0;
  while i < n  // targets: i, $Heap
    invariant 0 <= i <= n
    invariant unchanged(c)
  assert i == n;
  assert c.y == old(c.y);
  assert n == 0;  // error: should not be provable
}

method M8(c: C, n: nat)
  modifies c
{
  var i := 0;
  label L:
  while i < n  // targets: i, $Heap
    invariant 0 <= i <= n
    invariant unchanged@L(c)
  assert i == n;
  assert c.y == old(c.y);
  assert n == 0;  // error: should not be provable
}

method M9(c: C, n:nat)
  modifies c
{
  var k := c.y;
  var i := 0;
  while i < n  // targets: i, k
    invariant 0 <= i <= n
    invariant k == old(c.y)  // this is not a mention of the current heap
  assert k == old(c.y);
  assert k == c.y;  // should be provable, since heap was not havocked
  assert n == 0;  // error: should not be provable
}

method M10(c: C)
  modifies c
{
  var k := c.y;
  var i := 0;
  while i < 100  // targets: i, $Heap
    decreases c.m  // this mentions the heap
  assert k == c.y;  // error: should not be provable
}

method M11(c: C)
  modifies c
{
  var i := 0;
  while i < c.u  // targets: i
  assert c.y == old(c.y);  // fine, since c.u above is an immutable field
  assert i == c.u;  // error: should not be provable
}

method M12(c: C)
  modifies c
{
  var i := 0;
  while i < c.y  // targets: i, $Heap
  assert c.y == old(c.y);  // error: should not be provable
}

method M13(c: C)
  modifies c
{
  var i := 0;
  while i < 7  // targets: i, $Heap
    invariant allocated(c)  // this uses the heap
  assert c.y == old(c.y);  // error: should not be provable
}

// fresh

method H0a() returns (k: C) {
  var i := 0;
  k := new C;
  var k0 := k;
  while i < 7  // targets: i, k
    invariant fresh(k)  // this is not a use of the current heap
  assert fresh(k);
  // The following assertion is provable, because there's no indication that
  // the loop above modifies the heap and d0 is the only fresh object around.
  assert k == k0;
  assert i == 7;  // error: should not be provable
}

method H0b() returns (k: C) {
  var i := 0;
  var c := new C;  // one fresh object here
  k := new C;  // and another one here
  var k0 := k;
  while i < 7  // targets: i, k
    invariant fresh(k)  // this is not a use of the current heap
  assert fresh(k);
  assert k == k0 || k == c;  // yes, provable
  assert k == k0;  // error: no longer provable (cmp. H0a), because of the 2 fresh objects
  assert i == 7;  // error: should not be provable
}

method H0c() returns (k: C) {
  var i := 0;
  k := new C;  // and another one here
  var k0 := k;
  while i < 7 && k.y == k.y  // targets: i, k, $Heap
    invariant fresh(k)  // this is not a use of the current heap
  assert fresh(k);
  assert k == k0;  // error: no longer provable (cmp. H0a), because $Heap is a loop target
  assert i == 7;  // error: should not be provable
}

method H1(a: array<int>) returns (k: C)
  requires a.Length == 10
  modifies a
{
  var i := 0;
  k := new C;
  k.y := 12;
  while i < 7  // targets: i, $Heap
    invariant a[0] == old(a[0])  // this mentions the heap
  assert k.y == 12;  // error: should not be provable
}

method H2(a: array<int>) returns (k: C)
  requires a.Length == 10 && a[0] == 8
  modifies a
{
  var i := 0;
  k := new C;
  label L:
  k.y := 12;
  while i < 7  // targets: i
    invariant old(a[0]) == 8 == old@L(a[0])  // no mention of the heap
  assert k.y == 12;  // therefore, this is provable
}

method H3(a: array<int>) returns (k: C)
  requires a.Length == 10 && a[0] == 8
{
  var i := 0;
  k := new C;
  k.y := 12;
  while i < 7  // targets: i
    invariant i <= 7  // no mention of the heap
  assert k.y == 12;  // therefore, this is provable
}

method H4(a: array<int>) returns (k: C)
  requires a.Length == 10 && a[0] == 8
{
  var i := 0;
  k := new C;
  k.y := 12;
  while i < 7  // targets: i, k, $Heap
    invariant k.y % 2 == 0  // this mentions the heap
  assert k.y == 12;  // error: should not be provable
}

method H5() returns (k: C)
{
  var i := 0;
  k := new C;
  k.y := 12;
  var c := k;
  while i < 7  // targets: i, k, $Heap
    invariant k.y % 2 == 0
    modifies {}  // so, only objects allocated in loop can be modified
  assert c.y == 12;
  assert k.y == 12;  // error: should not be provable
}

method H6(c: C) returns (k: C)
  requires c.y == 3
{
  k := c;
  var i := 0;
  while i < 7  // targets: i, k, $Heap
    invariant k.y == 3  // this mentions the heap
    modifies {}  // loop bears a modifies clause
  assert old(allocated(k));  // error: k might be newly allocated by the loop
}

method H7(c: C) returns (k: C)
  requires c.u == 3
{
  k := c;
  var i := 0;
  while i < 7  // targets: i, k
    invariant k.u == 3  // this is a const field, so does not count as reading the heap
  assert old(allocated(k));  // yes, since heap is not havocked by the loop
}

// On entry

method E0(c: C) returns (k: C)
  modifies c
{
  k := c;
  var i := 0;
  while i < 7  // targets: i, k, $Heap
    invariant k.y == 3  // error: does not hold on entry
    modifies c
}

// Well-definedness

method W0(c: C) returns (k: C?)
  requires c.y == 3
  modifies c
{
  k := c;
  var i := 0;
  while i < 7  // targets: i, k, $Heap
    invariant k.y == 3  // error: k may be null
}

// fine-grained modifies clauses, and nested loops

class FineGrained {
  var f: int
  var g: int

  method R0(x: int)
    requires f <= x
    modifies `f
  {
    while 0 < f  // targets: $Heap
      invariant f <= x
    assert g == old(g);
  }

  method R1(x: int)
    requires f <= x
    modifies this
  {
    while 0 < f  // targets: $Heap
      invariant f <= x
      modifies `f
    assert g == old(g);
  }

  method R2(x: int)
    requires f <= x
    modifies this
  {
    while 0 < f
      invariant f <= x
      decreases f
      modifies `f
    {
      var i, prev := 0, f;
      while i < 7  // error: this modifies violates modifies of context
        modifies this
      f := prev - 1;
    }
  }

  method R3(x: int)
    requires f <= x
    modifies this
  {
    while 0 < f
      invariant f <= x
      decreases f
      modifies {}
    {
      var i := 0;
      while i < 7  // error: this modifies violates modifies of context
        modifies `f
      assert g == old(g);
      f := f - 1;
    }
  }

  method R4(c: FineGrained, x: int)
    requires this != c
    modifies this, c
  {
    var i := 0;
    while i < 7  // targets: i, $Heap
      invariant i <= 7
      modifies {}
    {
      var j := 0;
      while j < 7  // error: this modifies violates modifies of context
        modifies c
      assert g == old(g);
      i := i + 1;
    }
  }
}

// forall statements

method F0(S: set<int>, y: int)
{
  forall s | s in S
    ensures s < 0
  assert y in S ==> y < 0;
}

method F1(S: set<int>, y: int)
{
  forall s | s in S
    ensures s < 0
  assert y in S ==> y == -18;  // error: does not hold
}

ghost predicate P(y: int)

method F2() {
  forall y: int  // this once used to crash Dafny
    ensures P(y)

  forall x: int  // this once used to crash Dafny
}

// loop guard that definitely holds on entry to the loop

method GuardAlwaysHoldsOnEntry_BodyLessLoop() {
  // Without a loop body, we want the effect that the loop specification--that
  // is, the loop guard, the loop invariant, and the loop frame--says all there
  // is to say about the loop. Dafny supplies three 3 pieces to Boogie and then
  // lets Boogie's loop usual processing do the rest. If the guard necessarily
  // holds initially and this gets noticed by Boogie, then Boogie treats this as
  // no loop at all. That kind of cleverness is sound, but when demonstrating
  // the concepts of loop reasoning, it just looks confusing. Therefore, Dafny
  // counteracts this in its Boogie encoding of body-less loop, which is what
  // this method tests.
  var x := 20;
  while x < 20
    invariant x % 2 == 0
  assert x == 20;  // error (see comment above)
}

method GuardAlwaysHoldsOnEntry_LoopWithBody() {
  // When the Dafny program supplies a loop body, then Dafny allows Boogie to
  // be as clever as it wishes, as is demonstrated by this test case.
  var x := 20;
  while x < 20
    invariant x % 2 == 0
  {
    assert false;  // thanks to Boogie's abstract interpreter, the verifier knows we never get here
  }
  assert x == 20;  // ... and can prove this assertion
}
