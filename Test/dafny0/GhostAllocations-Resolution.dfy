// RUN: %exits-with 2 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ------- A constructor-less class can be allocated as either ghost or non-ghost

module ConstructorLessClass {
  class Cell {
    var data: int
  }

  method Cell0() returns (r: Cell) {
    var c := new Cell;
    ghost var g := new Cell;
    if * {
      r := c;
    } else {
      r := g; // error: cannot assign ghost to non-ghost
    }
  }
}

// ------- A class with a constructor is ghost/non-ghost depending on the constructor called

module Dual {
  class Either {
    constructor A(x: int) {
    }
    ghost constructor B(x: int) {
    }
  }

  method Either0() returns (r: Either) {
    var e := new Either.A(5);
    var g := new Either.B(5); // g is auto-ghost

    if * {
      r := e;
    } else {
      r := g; // error: cannot assign ghost to non-ghost
    }
  }

  method Either1(n: nat, ghost n': nat) {
    var e;
    ghost var g;
    e := new Either.A(n);
    e := new Either.A(n'); // error: cannot pass ghost to non-ghost
    g := new Either.B(n);
    g := new Either.B(n');
  }

  method Either2(n: nat) {
    var e;
    ghost var g;
    e := new Either.B(n); // error: ghost constructor can only be called in a ghost context
    g := new Either.A(n); // error: non-ghost constructor cannot be called in a ghost context
  }

  ghost method Either3(n: nat) {
    var e;
    e := new Either.B(n); // fine, since Either3 is a ghost context
    e := new Either.A(n); // error: non-ghost constructor cannot be called in a ghost context
  }

  class Cell {
    var x: Either
    ghost var y: Either
  }

  method AlternativeLhss() {
    var a := new object[10];
    a[0] := new Either.B(2); // error: cannot assign ghost to non-ghost

    var m := new object[10, 10];
    m[5, 3] := new Either.B(2); // error: cannot assign ghost to non-ghost

    var c := new Cell;
    c.x := new Either.B(2); // error: cannot assign ghost to non-ghost
    c.y := new Either.B(2);
  }
}

// ------- An array can be allocated as either ghost either non-ghost

module Arrays {
  method Array0(n: nat, ghost n': nat) {
    var a;
    ghost var g;
    a := new int[n];
    a := new int[n']; // error: cannot use ghost in this context
    g := new int[n];
    g := new int[n'];
  }

  method Array1(f: int -> real, ghost f': int -> real) {
    var a;
    ghost var g;
    a := new real[10](f);
    a := new real[10](f'); // error: cannot use ghost in this context
    g := new real[10](f);
    g := new real[10](f');
  }

  method Array2(n: nat, ghost n': nat, f: int -> real, ghost f': int -> real) returns (r: object) {
    // In the next line, b and d are auto-ghost
    var a, b, c, d := new real[n], new real[n'], new real[10](f), new real[10](f');
    if
    case true =>
      r := a;
    case true =>
      r := b; // error: cannot assign ghost to non-ghost
    case true =>
      r := c;
    case true =>
      r := d; // error: cannot assign ghost to non-ghost
  }

  method Array3(n: nat, ghost n': nat, f: int -> real, ghost f': int -> real) returns (r: object) {
    // In the next line, b, c, and d are auto-ghost
    var a, b, c, d := new real[n](f), new real[n'](f), new real[n](f'), new real[n'](f');
    if
    case true =>
      r := a;
    case true =>
      r := b; // error: cannot assign ghost to non-ghost
    case true =>
      r := c; // error: cannot assign ghost to non-ghost
    case true =>
      r := d; // error: cannot assign ghost to non-ghost
  }

  method Array4() returns (ghost r: array<int>) {
    ghost var a := new int[20];
    ghost var b := new int[] [2, 3, 5, 7, var k := 11; k, ghost var g := 13; g];
    ghost var c := new int[100](i => 2 * i);
    ghost var d := new int[] [2, 3, b[2], 7, 11, 13];
    r := a;
    r := b;
    r := c;
    r := d;
  }

  method Array5(ghost n: int) returns (ghost r: array<int>)
    requires n == 20
  {
    // a, b, c, d are auto-ghost
    var a := new int[n];
    var b := new int[] [2, 3, 5, 7, var k := 11; k, ghost var g := 13; g];
    var c := new int[100](Double);
    var d := new int[] [2, 3, b[2], 7, 11, 13];
    r := a;
    r := b;
    r := c;
    r := d;
  }

  function Double(i: int): int { 2 * i }
}

// ------- ghost constructors

module GhostConstructors0 {
  class G {
    const c: int
    ghost const d: int
    const e: int := 5
    ghost const f: int := 6

    ghost constructor (x: int) {
      e := 100; // error: cannot assign to const field that has a RHS
      f := 100; // error: cannot assign to const field that has a RHS
      new;
      c := 2; // error: cannot assign to const after "new;"
      d := 3; // error: cannot assign to const after "new;"
    }
  }
}

module GhostConstructors1 {
  class Cell {
    var data: int
  }

  class G {
    var a: int
    ghost var b: int
    const c: int
    ghost const d: int

    ghost constructor (x: int) {
      b, d := x, x + a;
      a := 2;
      c := 3;
      if x < 17 {
        Compiled(); // error: cannot call non-ghost from a ghost context
        Ghost();
        Lemma();
      }
      new;
      a := 0; // error: cannot assign to non-ghost after "new;" in ghost constructor
      b := 1;
      Compiled(); // error: cannot call non-ghost from a ghost context
      Ghost();
      Lemma();
    }

    static method Compiled()
    static ghost method Ghost()
    static lemma Lemma()
  }

  type GGG(0)

  class GhostableAutoInit {
    var g: GGG
    ghost var h: GGG

    constructor A(g: GGG) {
      this.g := g;
    }

    constructor B() { // definite-assignment rules are not satisfied, but that's check during verification (see GhostAllocations.dfy)
    }

    ghost constructor C(g: GGG) {
      this.g := g;
    }

    ghost constructor D() { // in a ghost context, we only need to know that g's type is nonempty (same as for h all along)
    }

    ghost constructor PostNew(c: GhostableAutoInit)
      modifies c
    {
      g := h; // fine before "new;"
      c.g := h; // error: cannot assign to non-ghost field of non-this
      print "hello\n"; // error: cannot use print in ghost context
      new;
      g := h; // error: after "new;", rules are as normal, so cannot assign to non-ghost field in this ghost context
      print "bye\n"; // error: cannot use print in ghost context
    }

    ghost constructor CalcInInitializationPhase() {
      var c0 := new Cell; // fine here
      var g0 := new G(5); // fine here
      calc {
        5;
      ==  { var c1 := new Cell; // error: cannot allocate inside calc hint
            var g1 := new G(5); // error: cannot allocate inside calc hint
          }
        2 + 3;
      }
      assert true by {
        var c2 := new Cell; // error: cannot allocate inside assert-by
        var g2 := new G(5); // error: cannot allocate inside assert-by
      }
      new;
    }
  }
}

module GhostInitializingMethods {
  class G {
    var data: int
    ghost var gata: int

    method CompiledInit(x: int) {
      gata := x;
      data := x;
    }

    ghost method GhostInit(x: int) {
      gata := x;
      data := x; // error: cannot assign to a non-ghost field in a ghost context
    }
  }

  method M() returns (g: G) {
    var a := new G.CompiledInit(5);
    var b := new G.GhostInit(5); // b is auto-ghost

    if * {
      g := a;
    } else {
      g := b; // error: cannot assign ghost to non-ghost
    }
  }
}

// ------- lemmas are not allowed to allocate any state

module Lemmas {
  class Cell {
    var data: int
  }

  class Point {
    constructor XY(x: real, y: real)
    ghost constructor Polar(theta: real, mag: real)
  }
  
  lemma A() {
    var o := new object; // error: lemma is not allowed to allocate state
    var c := new Cell; // error: lemma is not allowed to allocate state
  }

  lemma B() {
    var pt0 := new Point.XY(1.0, 0.0); // error: cannot call non-ghost constructor
    var pt1 := new Point.Polar(0.0, 1.0); // error: ... or a ghost constructor, for that matter
  }

  lemma C() {
    var a := new int[25]; // error: lemma is not allowed to allocate state
    var m := new real[640, 480]; // error: lemma is not allowed to allocate state
  }

  twostate lemma D() {
    var c := new Cell; // error: lemma is not allowed to allocate state
  }

  greatest lemma E() {
    var c := new Cell; // error: lemma is not allowed to allocate state
  }
}

// ------- ghost methods cannot be called from lemma/proof contexts

module GhostMethodVersusLemma {
  class Marker { }
  class Cell {
    var data: int
    ghost var m: Marker?
  }

  ghost method G(m: Marker)
    ensures exists c: Cell :: allocated(c) && fresh(c) && c.m == m
  {
    var c := new Cell;
    c.m := m;
  }

  method M0() {
    var m := new Marker;
    forall c: Cell | allocated(c)
      ensures c.m != m
    {
      assert old(allocated(c));
    }
    var x := (G(m); 3); // error: not allowed to call ghost method in an expression
    assert exists c: Cell :: allocated(c) && c.m == m;
    assert false;
  }

  method M1(ghost b: bool) {
    var m := new Marker;
    G(m);
    if b {
      G(m);
    }
    assert b by {
      G(m); // error: not allowed to call ghost method from a hint
    }
    assert false;
  }

  lemma GG(m: Marker)
    ensures exists c: Cell :: allocated(c) && fresh(c) && c.m == m
  {
    G(m); // error: not allowed to call ghost method from a lemma
  }

  method M2() {
    var m := new Marker;
    calc {
      5;
    ==  { G(m); } // error: not allowed to call ghost method from a hint
      7 - 2;
    }
  }

  lemma M3(m: Marker) {
    calc {
      5;
    ==  { G(m); } // error: not allowed to call ghost method from a lemma
      7 - 2;
    }
  }

  lemma Modify0() {
    var i := 0;
    while i < 10
      modifies {} // error: not allowed modifies clause in lemma context
    {
      i := i + 1;
    }
    while
      modifies {} // error: not allowed modifies clause in lemma context
    {
      case i < 20 => i := i + 1;
    }
    for j := 0 to 100
      modifies {} // error: not allowed modifies clause in lemma context
    {
    }
    ghost var S: set<object> := {};
    modify S; // error: not allowed modify statement in lemma context
    modify S { // error: not allowed modify statement in lemma context
    }
    var c := new Cell; // error: 'new' not allowed in lemma context
    c.m := null; // error: lemma is not allowed to make heap updates
  }
  ghost method Modify1() {
    assert true by {
      var i := 0;
      while i < 10
        modifies {} // error: not allowed modifies clause in lemma context
      {
        i := i + 1;
      }
      while
        modifies {} // error: not allowed modifies clause in lemma context
      {
        case i < 20 => i := i + 1;
      }
      for j := 0 to 100
        modifies {} // error: not allowed modifies clause in lemma context
      {
      }
      ghost var S: set<object> := {};
      modify S; // error: not allowed modify statement in lemma context
      modify S { // error: not allowed modify statement in lemma context
      }
      var c := new Cell; // error: 'new' not allowed in lemma context
    }
  }

  ghost method Modify2() {
    var i := 0;
    while i < 10
      modifies {}
    {
      i := i + 1;
    }
    while
      modifies {}
    {
      case i < 20 => i := i + 1;
    }
    for j := 0 to 100
      modifies {}
    {
    }
    ghost var S: set<object> := {};
    modify S;
    modify S {
    }
    var c := new Cell;
  }

  predicate IsBig(x: int) {
    100 <= x
  }

  method OrdinaryMethod()

  ghost method PlainGhostMethod()

  ghost method GhostMethodWithModifies(c: Cell)
    modifies c

  lemma Lemma()

  class Point {
    constructor XY(x: real, y: real)
    ghost constructor Polar(theta: real, mag: real)
  }
  
  method Modify3() {
    var c := new Cell;
    forall i
      ensures IsBig(i) ==> IsBig(i + 1)
    {
      var i := 0;
      while i < 10
        modifies {} // error: not allowed modifies clause in lemma context
      {
        i := i + 1;
      }
      while
        modifies {} // error: not allowed modifies clause in lemma context
      {
        case i < 20 => i := i + 1;
      }
      for j := 0 to 100
        modifies {} // error: not allowed modifies clause in lemma context
      {
      }
      ghost var S: set<object> := {};
      modify S; // error: not allowed modify statement in lemma context
      modify S { // error: not allowed modify statement in lemma context
      }

      OrdinaryMethod(); // error: cannot call non-ghost method from here
      PlainGhostMethod(); // error: cannot call ghost method from here
      GhostMethodWithModifies(c); // error: cannot call ghost method from here
      Lemma(); // fine

      var c := new Cell; // error: 'new' not allowed in lemma context
      var pt0 := new Point.XY(0.0, 0.0); // error: 'new' not allowed in lemma context
      ghost var pt1 := new Point.Polar(0.0, 1.0); // error: 'new' not allowed in lemma context
    }
  }
  
  method Modify4() {
    var c := new Cell;
    calc {
      200_000;
    ==  {
          var i := 0;
          while i < 10
            modifies {} // error: not allowed modifies clause in lemma context
          {
            i := i + 1;
          }
          while
            modifies {} // error: not allowed modifies clause in lemma context
          {
            case i < 20 => i := i + 1;
          }
          for j := 0 to 100
            modifies {} // error: not allowed modifies clause in lemma context
          {
          }
          ghost var S: set<object> := {};
          modify S; // error: not allowed modify statement in lemma context
          modify S { // error: not allowed modify statement in lemma context
          }

          OrdinaryMethod(); // error: cannot call non-ghost method from here
          PlainGhostMethod(); // error: cannot call ghost method from here
          GhostMethodWithModifies(c); // error: cannot call ghost method from here
          Lemma(); // fine

          var c := new Cell; // error: 'new' not allowed in lemma context
          var pt0 := new Point.XY(0.0, 0.0); // error: 'new' not allowed in lemma context
          ghost var pt1 := new Point.Polar(0.0, 1.0); // error: 'new' not allowed in lemma context
        }
      200_000;
    }
  }

  method Modify5(n: nat, ghost b: bool)
    requires n != 0
  {
    var a := new int[n];
    var cell := new Cell;
    var S := {cell};

    a[0] := 0;
    forall i | 0 <= i < n {
      a[i] := i;
    }

    cell.data := 0;
    forall c | c in S {
      c.data := 0;
    }

    cell.m := null;
    forall c | c in S {
      c.m := null;
    }

    if b {
      a[0] := 0; // error: ghost context cannot assign to non-ghost heap location
      forall i | 0 <= i < n {
        a[i] := i; // error: ghost context cannot assign to non-ghost heap location
      }

      cell.data := 0; // error: ghost context cannot assign to non-ghost heap location
      forall c | c in S {
        c.data := 0; // error: ghost context cannot assign to non-ghost heap location
      }

      cell.m := null;
      forall c | c in S {
        c.m := null;
      }
    }

    calc {
      2016;
    < {
        a[0] := 0; // error: cannot assign to heap in this lemma context
        forall i | 0 <= i < n { // error: cannot do aggregate heap update in this lemma context
          a[i] := i;
        }

        cell.data := 0; // error: a lemma context cannot update heap locations
        forall c | c in S { // error: cannot do aggregate heap update in this lemma context
          c.data := 0;
        }

        cell.m := null; // error: a lemma context cannot update heap locations
        forall c | c in S { // error: cannot do aggregate heap update in this lemma context
          c.m := null;
        }
      }
      2020;
    }

    assert true by {
      a[0] := 0; // error: cannot assign to heap in this lemma context
      forall i | 0 <= i < n { // error: cannot do aggregate heap update in this lemma context
        a[i] := i;
      }

      cell.data := 0; // error: a lemma context cannot update heap locations
      forall c | c in S { // error: cannot do aggregate heap update in this lemma context
        c.data := 0;
      }

      cell.m := null; // error: a lemma context cannot update heap locations
      forall c | c in S { // error: cannot do aggregate heap update in this lemma context
        c.m := null;
      }
    }

    forall j | 0 <= j < n
      ensures IsBig(j) ==> IsBig(j + 1)
    {
      a[0] := 0; // error: cannot assign to heap in this lemma context
      forall i | 0 <= i < n { // error: cannot do aggregate heap update in this lemma context
        a[i] := i;
      }

      cell.data := 0; // error: a lemma context cannot update heap locations
      forall c | c in S { // error: cannot do aggregate heap update in this lemma context
        c.data := 0;
      }

      cell.m := null; // error: a lemma context cannot update heap locations
      forall c | c in S { // error: cannot do aggregate heap update in this lemma context
        c.m := null;
      }
    }
  }
}

// --------------- assignments ------------------------------

module Assignments {
  class Cell { }
  class Point {
    constructor XY()
    ghost constructor Polar()
  }

  method M0(n: nat, init: int -> int) {
    var c, pt0, pt1, arr;
    c := new Cell;
    pt0 := new Point.XY();
    pt1 := new Point.Polar(); // error: cannot use ghost constructor to assign compiled variable
    arr := new int[n];
    arr := new int[] [n];
    arr := new int[10](init);
  }

  method M1(ghost n: nat, ghost init: int -> int) {
    ghost var c, pt0, pt1;
    var arr;
    c := new Cell;
    pt0 := new Point.XY(); // error: cannot use non-ghost constructor to assign ghost variable
    pt1 := new Point.Polar();
    arr := new int[n]; // error: cannot use ghost in RHS
    arr := new int[] [n]; // error: cannot use ghost RHS display
    arr := new int[10](init); // error: cannot use ghost RHS initializer
  }

  ghost method M2(n: nat, init: int -> int) {
    var c, pt0, pt1, arr;
    c := new Cell;
    pt0 := new Point.XY(); // error: cannot use non-ghost constructor in ghost context
    pt1 := new Point.Polar();
    arr := new int[n];
    arr := new int[] [n];
    arr := new int[10](init);
  }

  lemma M3(n: nat, init: int -> int) {
    var c, pt0, pt1, arr;
    c := new Cell; // error: cannot use 'new' in lemma context
    pt0 := new Point.XY(); // error (x2): cannot use 'new' in lemma context (and cannot call constructor)
    pt1 := new Point.Polar(); // error (x2): cannot use 'new' in lemma context (and cannot call constructor)
    arr := new int[n]; // error: cannot use 'new' in lemma context
    arr := new int[] [n]; // error: cannot use 'new' in lemma context
    arr := new int[10](init); // error: cannot use 'new' in lemma context
  }
}
