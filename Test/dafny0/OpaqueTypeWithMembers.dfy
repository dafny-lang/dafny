// RUN: %exits-with 4 %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Opaque {
  const y: int
  const z := 25
  function F(): int { z }
  method G(a: int) returns (b: int) { b := a + this.y; }

  lemma LemmaF25(n: nat)
    ensures z == 25
  {
    var zz := z + y;
    assert zz - y == 25;
  }

  twostate function H(a: array<int>): int {
    if a.Length == 100 then old(a[3]) + y + 2 else 0
  }
  twostate lemma Two(a: array<int>) returns (u: int)
    requires a.Length == 100
    requires old(y + a[3]) == y
    ensures old(a[3] + y) == y
  {
    u := old(y + a[3]);
    var f := old(F()); // warning: old has no effect (since F has no reads clause)
    var u' := y + a[3];
    var f' := F();
  }

  least predicate Q(u: int) {
    y + z < 20 || Q(u + 1)
  }
  least lemma QL(u: int)
    requires Q(u)
    ensures y + z < 20
  {
    var w := y + z;
  }
}

type StaticOpaque {
  static const y: int
  static const z := 25
  static function F(): int { z }
  static method G(a: int) returns (b: int) { b := a + y; }

  static lemma LemmaF25(n: nat)
    ensures z == 25
  {
    var zz := z + y;
    assert zz - y == 25;
  }

  static twostate function H(a: array<int>): int {
    if a.Length == 100 then old(a[3]) + y + 2 else 0
  }
  static twostate lemma Two(a: array<int>) returns (u: int)
    requires a.Length == 100
    requires old(y + a[3]) == y
    ensures old(a[3] + y) == y
  {
    u := old(y + a[3]);
    var f := old(F()); // warning: old has no effect (since F has no reads clause)
    var u' := y + a[3];
    var f' := F();
  }

  static least predicate Q(u: int) {
    y + z < 20 || Q(u + 1)
  }
  static least lemma QL(u: int)
    requires Q(u)
    ensures y + z < 20
  {
    var w := y + z;
  }
}

type OpaqueErrors {
  const y: int
  const z := 25
  function F(): int { 100 / z + 100 / y }  // error: division by zero
  method G(a: int) returns (b: int) { b := a + 100 / this.y; }  // error: division by zero

  twostate function H(a: array<int>): int {
    old(a[3]) + y + 2  // error: index out of bounds
  }
  twostate lemma Two(a: array<int>) returns (u: int)
    requires old(y + a[3]) == y  // error: index out of bounds
    ensures old(a[3] + y) == y
  {
    u := old(y + a[2]);  // error: index out of bounds
    var f := old(F()); // warning: old has no effect (since F has no reads clause)
    var u' := y + a[2];
    var f' := F();
  }

  least predicate Q(u: int) {
    100 / y + z < 20 || Q(u + 1)  // error: division by zero
  }
  least lemma QL(u: int)
    requires Q(u) && y != 0
    ensures 100 / y + z < 20
  {
    var w := y + 20 / z;
    var w' := 20 / (y + 1);  // error: division by zero
  }
}

type FailureCompatible(0) {
  const c: int
  predicate method IsFailure() { c < 10 }
  function method PropagateFailure(): int
    requires IsFailure()
  {
    100 / (c - 10)
  }
  function method Extract(): real
    requires !IsFailure()
  {
    100.0 / c as real
  }
}

method P(t: FailureCompatible) {
  var b := t.IsFailure();
  if t.c < 10 {
    assert b;
    var pf := t.PropagateFailure();
  } else {
    assert !b;
    var e := t.Extract();
  }
}

method P'(t: FailureCompatible) {
  if t.c < 10 {
    var e := t.Extract();  // error: precondition failure
  } else {
    var pf := t.PropagateFailure();  // error: precondition failure
  }
}

method M() returns (r: FailureCompatible) {
  r :| true;
}
