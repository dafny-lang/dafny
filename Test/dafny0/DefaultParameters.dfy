// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<T> = Nil | Cons(T, tail: List<T> /* := Nil*/)

method M(a: int, b: int) returns (r: int)
  ensures r == a + 2 * b
{
  r := a + 2 * b;
}

function method F(a: int, b: int, c: int): int
{
  a + 2 * b + 3 * c
}

class Cell<U> {
  var value: U
  constructor (u: U)
    ensures value == u
  {
    value := u;
  }
}

iterator Iter(a: int, b: int) yields (z: int) {
}

method ParsingActualBindings() {
  var xs0 := Cons(5, tail := Cons(7, Nil));
  var tuple0 := (1 := 10, 0 := 300);
  var r0 := M(100, b := 60);
  var x0 := F(200, c := 20, b := 10);
  var c0 := new Cell(u := 75);
  var iter0 := new Iter(10, b := 20);

  var xs1 := Cons(5, Cons(7, Nil));
  var tuple1 := (300, 10);
  var r1 := M(100, 60);
  var x1 := F(200, 10, 20);
  var c1 := new Cell(75);
  var iter1 := new Iter(10, 20);

  assert xs0 == xs1;
  assert tuple0 == tuple1;
  assert r0 == r1;
  assert x0 == x1;
  assert c0.value == c1.value;
  assert iter0.a == iter1.a && iter0.b == iter1.b;
}
