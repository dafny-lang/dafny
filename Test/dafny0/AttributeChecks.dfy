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
    {:dt k, this} Blue | {:dt 50} Green // error (x2): k is unknown, this is not allowed

  datatype {:dt 0} {:dt false + 3} AnotherDatatype = // error: false + 3 is ill-typed
    | {:dt 50} Blue | {:dt k, this} Green // error (x2): k is unknown, this is not allowed

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

  method LocalVariablesAndAssignments(opt: Option<int>, mustHave: MustHave<int>) returns (r: Option<int>) {
    // variables declared with attributes
    var
      {:boolAttr false + 3} a: int, // error: false + 3 is ill-typed
      {:boolAttr false + 3} b: int; // error: false + 3 is ill-typed

    // simple assignments, where each RHS has an attribute
    var x, y :=
      10 {:boolAttr false + 3}, // error: false + 3 is ill-typed
      20 {:boolAttr false + 3}; // error: false + 3 is ill-typed
    x, y :=
      10 {:boolAttr false + 3}, // error: false + 3 is ill-typed
      20 {:boolAttr false + 3}; // error: false + 3 is ill-typed

    // method call, where either the variable or the RHS has an attribute
    var {:boolAttr false + 3} u0 := If(13); // error: false + 3 is ill-typed
    var u1 := If(13) {:boolAttr false + 3}; // error: false + 3 is ill-typed
    u1 := If(13) {:boolAttr false + 3}; // error: false + 3 is ill-typed

    // arbitrary assignment, where either the variable or the RHS has an attribute
    var {:boolAttr false + 3} k0: int := *; // error: false + 3 is ill-typed
    var k1: int := * {:boolAttr false + 3}; // error: false + 3 is ill-typed
    k1 := * {:boolAttr false + 3}; // error: false + 3 is ill-typed

    // allocation, where either the variable or the RHS has an attribute
    var {:boolAttr false + 3} c0 := new CClass; // error: false + 3 is ill-typed
    var c1 := new CClass {:boolAttr false + 3}; // error: false + 3 is ill-typed
    c1 := new CClass {:boolAttr false + 3}; // error: false + 3 is ill-typed
    var {:boolAttr false + 3} d0 := new DClass(); // error: false + 3 is ill-typed
    var d1 := new DClass() {:boolAttr false + 3}; // error: false + 3 is ill-typed
    d1 := new DClass() {:boolAttr false + 3}; // error: false + 3 is ill-typed

    // assign-such-that, where variable has an attribute
    var s := {101};
    var {:boolAttr false + 3} w0 :| w0 in s; // error: false + 3 is ill-typed
    var
      {:boolAttr false + 3} w1, // error: false + 3 is ill-typed
      {:boolAttr false + 3} w2 // error: false + 3 is ill-typed
      :| w1 in s && w2 in s;

    // assign-such-that, where assume has an attribute
    w1, w2 :| assume {:boolAttr false + 3} w1 in s && w2 in s; // error: false + 3 is ill-typed

    // :- with expression RHS, where variable declarations have attributes
    var {:boolAttr false + 3} f0 :- opt;
    var
      {:boolAttr false + 3} f1, // error: false + 3 is ill-typed
      {:boolAttr false + 3} f2 // error: false + 3 is ill-typed
      :- opt, true;
    // :- with call RHS, where variable declarations have attributes
    var {:boolAttr false + 3} f3 :- GiveOption();
    var
      {:boolAttr false + 3} f4, // error: false + 3 is ill-typed
      {:boolAttr false + 3} f5 // error: false + 3 is ill-typed
      :- GiveOptions();

    // :- with expression RHS, where RHSs have attributes
    var g0 :- opt {:boolAttr false + 3}; // error: false + 3 is ill-typed
    var g1, g2 :-
      opt {:boolAttr false + 3}, // error: false + 3 is ill-typed
      true {:boolAttr false + 3}; // error: false + 3 is ill-typed
    var g3, g4, g5 :-
      opt {:boolAttr false + 3}, // error: false + 3 is ill-typed
      true {:boolAttr false + 4}, // error: false + 4 is ill-typed
      true {:boolAttr false + 5}; // error: false + 5 is ill-typed
    // :- with call RHS, where variable declarations have attributes
    var g6 :- GiveOption() {:boolAttr false + 3}; // error: false + 3 is ill-typed
    var g7, g8 :- GiveOptions() {:boolAttr false + 3}; // error: false + 3 is ill-typed

    :- mustHave {:boolAttr false + 3}; // error: false + 3 is ill-typed
    :- GiveMustHave() {:boolAttr false + 3}; // error: false + 3 is ill-typed

    // :- with expression RHS, where assert/assume/expect has attributes
    var p0 :- assert {:boolAttr false + 3} opt; // error: false + 3 is ill-typed
    var p1 :- assume {:boolAttr false + 3} opt; // error: false + 3 is ill-typed
    var p2 :- expect {:boolAttr false + 3} opt; // error: false + 3 is ill-typed
    p0 :- assert {:boolAttr false + 3} opt; // error: false + 3 is ill-typed
    p1 :- assume {:boolAttr false + 3} opt; // error: false + 3 is ill-typed
    p2 :- expect {:boolAttr false + 3} opt; // error: false + 3 is ill-typed

    // :- with call RHS, where variable declarations have attributes
    var q0 :- assert {:boolAttr false + 3} GiveOption(); // error: false + 3 is ill-typed
    var q1 :- assume {:boolAttr false + 3} GiveOption(); // error: false + 3 is ill-typed
    var q2 :- expect {:boolAttr false + 3} GiveOption(); // error: false + 3 is ill-tyqed
    q0 :- assert {:boolAttr false + 3} GiveOption(); // error: false + 3 is ill-tyqed
    q1 :- assume {:boolAttr false + 3} GiveOption(); // error: false + 3 is ill-tyqed
    q2 :- expect {:boolAttr false + 3} GiveOption(); // error: false + 3 is ill-typed

    // let-such-that with an attribute
    var i := var
      a, b {:boolAttr false + 3} :| a == 0 && b == 1; // error: false + 3 is ill-typed
      100;
  }

  function ExtendedPrintExpr(): int {
    var
      a, b {:boolAttr false + 3} :| a == 0 && b == 1; // error: false + 3 is ill-typed
      100
  }

  class CClass {
  }
  class DClass {
    constructor () { }
  }

  method GiveOption() returns (r: Option<int>)
  method GiveOptions() returns (r: Option<int>, s: int)
  method GiveMustHave() returns (r: MustHave<int>)

  datatype Option<+T> = None | Some(value: T) {
    predicate method IsFailure() {
      None?
    }
    function method PropagateFailure<U>(): Option<U>
      requires None?
    {
      None
    }
    function method Extract(): T
      requires Some?
    {
      value
    }
  }

  datatype MustHave<+T> = HasIt | DoesNotHave(value: T) {
    predicate method IsFailure() {
      DoesNotHave?
    }
    function method PropagateFailure(): Option<T>
      requires DoesNotHave?
    {
      None
    }
  }
}

module
  {:myAttr false + 3} // error: false + 3 is ill-typed
  {:myAttr old(3)} // error: old is not allowed here
  {:myAttr k} // error: k is not in scope here
  Modu
{
}

module TwoStateAttributes {
  class C {
    var data: int

    function {:myAttr old(data), x, r} F(x: int): (r: int) // error: old not allowed in this context

    twostate function {:myAttr old(data), x, r} F2(x: int): (r: int) // old is allowed

    lemma {:myAttr old(data), x, y} L(x: int) returns (y: int) // error: old not allowed in this context

    twostate lemma {:myAttr old(data), x, y} L2(x: int) returns (y: int) // old is allowed

    method {:myAttr old(data), x, y} M(x: int) returns (y: int) // error: old not allowed in this context

    least predicate {:myAttr old(data), x} LP(x: int) // error: old not allowed in this context

    least lemma {:myAttr old(data), x} LL(x: int) // error: old not allowed in this context
  }
}

module TopLevelAttributes {
  // ---- iterator

  // an attribute on an iterator is allowed to refer to the in-parameters of the iterator, but not to "this" or to the yield-parameters.
  iterator
    {:myAttr x}
    {:myAttr y} // error: y is not allowed here
    {:myAttr this} // error: this is not allowed here
    {:myAttr ys} // error: ys is not allowed here (because "this" isn't)
    {:myAttr old(arr[0])} // error: "old" is not allowed here
    Iterator(x: int, arr: array<int>) yields (y: int)
    requires arr.Length != 0

  // ---- opaque type

  type
    {:myAttr this} // error: this is not allowed here
    {:myAttr N} // error: N unresolved
    Opaque
  {
    const N: int
  }

  // ---- subset type

  type {:myAttr this} Subset = x: int | true // error: "this" is not allowed here

  // ---- type synonym

  type {:myAttr this} Synonym = int // error: "this" is not allowed here

  // ---- newtype

  newtype
    {:myAttr this} // error: this is not allowed
    {:myAttr N} // error: N unresolved
    Newtype = x: int | true
  {
    const N: int
  }

  // ---- trait

  trait
    {:myAttr this} // error: this is not allowed
    {:myAttr x} // error: x unresolved
    Trait
  {
    var x: int
  }

  // ---- class

  class
    {:myAttr this} // error: this is not allowed
    {:myAttr x} // error: x unresolved
    Class
  {
    var x: int
  }

  // ---- datatype

  datatype
    {:myAttr this} // error: this is not allowed here
    {:myAttr Ctor?} // error: Ctor? unresolved
    {:myAttr y} // error: y unresolved
    {:myAttr N} // error: N unresolved
    Datatype = Ctor(y: int)
  {
    const N: int
  }

  // ---- codatatype

  codatatype
    {:myAttr this} // error: this is not allowed here
    {:myAttr Ctor?} // error: Ctor? unresolved
    {:myAttr y} // error: y unresolved
    {:myAttr N} // error: N unresolved
    CoDatatype = Ctor(y: int)
  {
    const N: int
  }
}

module TopLevelAttributesModule {
  // ---- module

  module {:myAttr this} Module { // error: "this" is not allowed here
  }
}
