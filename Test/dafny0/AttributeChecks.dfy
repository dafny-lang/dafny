// RUN: %dafny /print:"%t.print" /dprint:- /compile:0 /env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method If(n: int) returns (k: int)
{
  var i := 0;
  if {:split true} i < n {
    if {:split 1 + 0} true {}
  }
  else if {:split false} i > n {}
  else {:split true} {}
}

method IfAlt(n: int) returns (k: int)
{
  var i := 0;
  if {:split true}
  case {:split 1 + true} i < n => // error: 1 + true is ill-typed
    if {:split 1 + k} true {}
  case {:split false} i > n  => {}
  return 2;
}

method While(n: int) returns (k: int)
{
  var f: int -> int := x => x;
  var i := 0;
  while {:split true} {:split true + k} i < n // error: true + k is ill-typed
    invariant forall u :: f(u) == u + i
  {
  }
  return 2;
}

method WhileAlt(n: int) returns (k: int)
{
  var i := 0;
  var f: int -> int := x => x;
  while {:split}
    invariant forall u :: f(u) == u + i
  {
    case {:split 1 + true} i < n  => {} // error:  1 + true is ill-typed
    case {:split false} i > n => return 2;
  }
}

datatype List<T> = Nil | Cons (hd:T, tl: List<T>)
method Match(xs: List<int>) returns (r: int)
{
  match {:split 1} xs {
    case {:split false} Cons(y, z) => return y;
    case {:split 1 + false} Nil => return 0; // error:  1 + false is ill-typed
  }
}

function method CaseExpr(r: List<int>): List<int>
{
  match r {
    case Nil => Nil
    case {:ignore 3 + true} Cons(h, Nil) => Nil // error:  3 + true is ill-typed
    case {:ignore false} Cons(h, t) => CaseExpr(t)
  }
}

method Calc(x: int, y: int)
{
  calc {:split 1} {:split 1 + false} { // error:  1 + false is ill-typed
    x + y;
    { assume x == 0; }
    y;
  }
  assert x == 0; // OK: follows from x + y == y;
}

method ForAll(i: int, j: int, arr: array2<int>)
{
  forall i , j {:split 1 + false} {:split i + j}  | i in {-3, 4} && j in {1, 2}  { // error:  1 + false is ill-typed
    arr[i, j] := 0;
  }
}

method AssertBy(x: int, y: int)
{
  assert {:split false + x} {:split} x == 6 by {  // error:  false + x is ill-typed
    assume x == 6;
    assume y == 8;
  }
  assert {:split} y == 8;
}

method For(lo: int, hi: int) returns (k: int)
  requires lo <= hi
{
  var f: int -> int := x => x;
  for {:split i} {:split true + k} i := lo to hi // error: true + k is ill-typed
    invariant forall u :: f(u) == u + i
  {
  }
  return 2;
}

datatype {:dt 0} {:dt false + 3} Datatype = // error: false + 3 is ill-typed
  {:dt k} Blue | {:dt 50} Green // error: k is unknown

datatype {:dt 0} {:dt false + 3} AnotherDatatype = // error: false + 3 is ill-typed
  | {:dt 50} Blue | {:dt k} Green // error: k is unknown
