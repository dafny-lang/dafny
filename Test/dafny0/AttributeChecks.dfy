// RUN: %exits-with 2 %dafny /print:"%t.print" /dprint:- /compile:0 /env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module JustAboutEverything {
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

  function FAttr(x: int): int
    requires {:myAttr false + 3} true // error: false + 3 is ill-typed
    ensures {:myAttr false + 3} true // error: false + 3 is ill-typed
    decreases {:myAttr false + 3} x // error: false + 3 is ill-typed
  {
    10
  }

  function GAttr(x: int): int
    requires {:myAttr old(3)} true // error: old is not allowed here
    ensures {:myAttr old(3)} true // error: old is not allowed here
    decreases {:myAttr old(3)} x // error: old is not allowed here
  {
    10
  }

  function HAttr(x: int): (r: int)
    requires {:myAttr x, r} true // error: r is not in scope here
    ensures {:myAttr x, r} true
    decreases {:myAttr x, r} x // error: r is not in scope here
  {
    10
  }

  twostate function F2Attr(x: int): int
    requires {:myAttr false + 3} true // error: false + 3 is ill-typed
    ensures {:myAttr false + 3} true // error: false + 3 is ill-typed
    decreases {:myAttr false + 3} x // error: false + 3 is ill-typed
  {
    10
  }

  twostate function G2Attr(x: int): int
    requires {:myAttr old(3)} true
    ensures {:myAttr old(3)} true
    decreases {:myAttr old(3)} x
  {
    10
  }

  twostate function H2Attr(x: int): (r: int)
    requires {:myAttr x, r} true // error: r is not in scope here
    ensures {:myAttr x, r} true
    decreases {:myAttr x, r} x // error: r is not in scope here
  {
    10
  }

  method MAttr(x: int) returns (y: int)
    requires {:myAttr false + 3} true // error: false + 3 is ill-typed
    modifies {:myAttr false + 3} {} // error: false + 3 is ill-typed
    ensures {:myAttr false + 3} true // error: false + 3 is ill-typed
    decreases {:myAttr false + 3} x // error: false + 3 is ill-typed
  {
  }

  method NAttr(x: int) returns (y: int)
    requires {:myAttr old(3)} true // error: old is not allowed here
    modifies {:myAttr old(3)} {} // error: old is not allowed here
    ensures {:myAttr old(3)} true
    decreases {:myAttr old(3)} x // error: old is not allowed here
  {
  }

  method OAttr(x: int) returns (y: int)
    requires {:myAttr x, y} true // error: y is not in scope here
    modifies {:myAttr x, y} {} // error: y is not in scope here
    ensures {:myAttr x, y} true
    decreases {:myAttr x, y} x // error: y is not in scope here
  {
  }

  twostate lemma M2Attr(x: int) returns (y: int)
    requires {:myAttr false + 3} true // error: false + 3 is ill-typed
    modifies {:myAttr false + 3} {} // error (x2): false + 3 is ill-typed, and twostate lemma cannot have modifies clause
    ensures {:myAttr false + 3} true // error: false + 3 is ill-typed
    decreases {:myAttr false + 3} x // error: false + 3 is ill-typed
  {
  }

  twostate lemma N2Attr(x: int) returns (y: int)
    requires {:myAttr old(3)} true
    modifies {:myAttr old(3)} {} // error (x2): old is not allowed here, and twostate lemma cannot have modifies clause
    ensures {:myAttr old(3)} true
    decreases {:myAttr old(3)} x // error: old is not allowed here
  {
  }

  twostate lemma O2Attr(x: int) returns (y: int)
    requires {:myAttr x, y} true // error: y is not in scope here
    modifies {:myAttr x, y} {} // error (x2): y is not in scope here, and twostate lemma cannot have modifies clause
    ensures {:myAttr x, y} true
    decreases {:myAttr x, y} x // error: y is not in scope here
  {
  }

  iterator Iter(x: int) yields (y: int)
    requires {:myAttr false + 3} true // error: false + 3 is ill-typed
    yield requires {:myAttr false + 3} true // error: false + 3 is ill-typed
    modifies {:myAttr false + 3} {} // error: false + 3 is ill-typed
    yield ensures {:myAttr false + 3} true // error: false + 3 is ill-typed
    ensures {:myAttr false + 3} true // error: false + 3 is ill-typed
    decreases {:myAttr false + 3} x // error: false + 3 is ill-typed
  {
  }

  iterator Jter(x: int) yields (y: int)
    requires {:myAttr old(3)} true // error: old is not allowed here
    yield requires {:myAttr old(3)} true // error: old is not allowed here
    modifies {:myAttr old(3)} {} // error: old is not allowed here
    yield ensures {:myAttr old(3)} true
    ensures {:myAttr old(3)} true
    decreases {:myAttr old(3)} x // error: old is not allowed here
  {
  }

  iterator Kter(x: int) yields (y: int)
    requires {:myAttr x, y, ys} true // error (x2): y and ys are not in scope here
    yield requires {:myAttr x, y, ys} true // these are allowed (but it would be weird for anyone to use y and ys here)
    modifies {:myAttr x, y, ys} {} // error (x2): y and ys are not in scope here
    yield ensures {:myAttr x, y, ys} true
    ensures {:myAttr x, y, ys} true
    decreases {:myAttr x, y, ys} x // error (x2): y and ys are not in scope here
  {
  }

  method ModifyStatement(s: set<object>) {
    modify {:myAttr false + 3} s; // error: false + 3 is ill-typed
  }
}

module
  {:myAttr false + 3} // error: false + 3 is ill-typed
  {:myAttr old(3)} // error: old is not allowed here
  {:myAttr k} // error: k is not in scope here
  Modu
{
}
