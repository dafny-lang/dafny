// RUN: %exits-with 4 %dafny /compile:0 /typeSystemRefresh:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Even = u | u % 2 == 0

method M0(n: nat, e: Even) {
  var x; // nat
  x := n;
  x := n;

  var y; // int
  y := e;
  y := n;

  var z; // int
  z := n + n;

  x, y, z := *, *, *;
  if {
  case true =>
    assert 0 <= x;
  case true =>
    assert 0 <= y; // error: y is an int
  case true =>
    assert y % 2 == 0; // error: y is an int
  case true =>
    assert 0 <= z; // error: z is an int
  }
}

method M1() {
  var arr;
  arr := new [100];
  var y;
  y := arr[0] + 15;

  arr, y := *, *;
  var obj: object? := arr;
  assert obj != null;
  assert 0 <= y; // error: y is an int
}

method M2(ms: multiset<real>, m0: map<bool, nat>, m1: imap<real, nat>)
  requires true in m0.Keys
  requires 5.90 in m1.Keys
{
  var z;
  var nrr := new nat[100];
  z := nrr[0];
  var matrix := new nat[100, 100];
  z := matrix[2, 3];
  z := ms[3.19];
  z := m0[true];
  z := m1[5.90];

  z := *;
  assert 0 <= z;
}

method M3(s: seq<nat>, arr: array<nat>)
  requires 10 <= |s| && 10 <= arr.Length
{
  // variables a, b, c, x, y, z, w have type seq<nat>
  var a;
  a := s[..10];
  var b;
  b := s[0..];
  var c;
  c := s[0..10];

  var x;
  x := arr[..10];
  var y;
  y := arr[0..];
  var z;
  z := arr[0..10];
  var w;
  w := arr[..];

  var k;
  k := a[0];
  k := b[0];
  k := c[0];
  k := x[0];
  k := y[0];
  k := z[0];
  k := w[0];
  k := *;
  assert 0 <= k;
}

method M4(i: int, n: nat, b: bool) {
  var x; // nat
  x := if b then n else n;
  var y; // int
  y := if b then i else n;
  var z; // int
  z := if b then n else i;

  x, y, z := *, *, *;
  if {
    case true =>
      assert 0 <= x;
    case true =>
      assert 0 <= y; // error: y is int
    case true =>
      assert 0 <= z; // error: z is int
  }
}

datatype List = Nil | Cons(head: nat, tail: List)

type NatA = x: nat | 10 <= x < 20 witness *
type NatB = x: nat | 20 <= x < 30 witness *
type NatC = x: nat | 30 <= x < 40 witness *

method M5(list: List, a: NatA, b: NatB, c: NatC) {
  var x; // nat
  match list {
    case Nil =>
      x := a;
    case Cons(_, Nil) =>
      x := b;
    case _ =>
      x := c;
  }

  x := *;
  if {
    case true =>
      assert 0 <= x;
    case true =>
      assert 10 <= x; // error: x is nat
    case true =>
      assert 20 <= x; // error: x is nat
    case true =>
      assert 30 <= x; // error: x is nat
  }
}

method M6(list: List, a: NatA, b: NatB, c: NatC) {
  var x; // nat
  x :=
    match list
    case Nil => a
    case Cons(_, Nil) => b
    case _ => c;

  x := *;
  if {
    case true =>
      assert 0 <= x;
    case true =>
      assert 10 <= x; // error: x is nat
    case true =>
      assert 20 <= x; // error: x is nat
    case true =>
      assert 30 <= x; // error: x is nat
  }
}
