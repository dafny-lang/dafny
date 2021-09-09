// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Cell {
  var data: int
}

method M() returns (c: Cell)
  ensures fresh(c)

ghost method G() returns (c: Cell)
  ensures fresh(c)

lemma L() returns (c: Cell)
  ensures fresh(c)

twostate lemma L2() returns (c: Cell)
  ensures fresh(c)

predicate P(c: Cell)
least lemma Least()
  ensures exists c: Cell :: P(c) && fresh(c)

method Caller() {
  if
  case true =>
    var c := M();
    assert false; // error
  case true =>
    var c := G();
    assert false; // error
  case true =>
    var c := L();
    assert false; // unreachable, since lemma's postcondition is untenable
  case true =>
    var c := L2();
    assert false; // unreachable, since lemma's postcondition is untenable
  case true =>
    Least();
    ghost var c :| P(c) && fresh(c);
    assert false; // unreachable, since lemma's postcondition is untenable
  case true =>
    Least#[10]();
    ghost var c :| P(c) && fresh(c);
    assert false; // unreachable, since lemma's postcondition is untenable
}

class CellWrapper {
  var c: Cell
  constructor (c: Cell) {
    this.c := c;
  }
  ghost constructor Gh(c: Cell) {
    this.c := c;
  }
}

method Modify0(w: CellWrapper)
  modifies w
{
  modify w;
  assume fresh(w.c);
  assert false; // error: assuming fresh(w.c) does not lead to any contradiction
}

method Modify1(w: CellWrapper)
  modifies w
{
  assume fresh(w.c);
  assert false; // unreachable, due to the previous assumption
}

method Modify2() {
  modify {};
  assume exists c: Cell :: P(c) && fresh(c);
  assert false; // error: assuming the body-less modify statement allocates a Cell does not lead to any contradiction
}

ghost method Modify3() {
  modify {};
  assume exists c: Cell :: P(c) && fresh(c);
  assert false; // error: assuming the body-less modify statement allocates a Cell does not lead to any contradiction
}

lemma Modify4() {
  // The following "modify" statement is rather useless, since there's nothing a body for this "modify"
  // statement could do--a lemma is not allowed to allocate anything. If the verifier knew this fact, it
  // would realize that the subsequent assumption is "false", and thus it would be able to prove that
  // the assertion is unreachable. However, handling this special case in the verifier just for the purpose
  // of supporting this useless statement ain't worth it. Thus, the verifier will generate an error for
  // the assertion below.
  modify {};
  assume exists c: Cell :: P(c) && fresh(c);
  assert false; // error: the verifier doesn't know this statement cannot be reached
}

method ModifyBody0(w: CellWrapper)
  modifies w
{
  modify w {
    w.c := new Cell;
    w.c.data := 15;
  }
  assert fresh(w.c);
  assert false; // error
}

method ModifyBody1(w: CellWrapper)
  modifies w
{
  var c: Cell;
  modify {} {
    c := new Cell;
    c.data := 15;
  }
  assert fresh(c);
  assert false; // error
}

// ------------------- new -------------------

method SimpleNew() {
  ghost var c: Cell;
  c := new Cell;

  ghost var w: CellWrapper;
  w := new CellWrapper.Gh(c);

  ghost var arr: array<int>, m: array2<real>;
  arr := new int[20];
  m := new real[2, 390];

  var arr': array<int>, m': array2<real>;
  arr' := new int[20];
  m' := new real[2, 390];
  arr, m := arr', m';
}

type GGG(00)

class GhostableNonempty {
  var g: GGG
  ghost var h: GGG

  constructor A(g: GGG) {
    this.g := g;
  }

  constructor B() {
  } // error: g is never assigned

  ghost constructor C(g: GGG) {
    this.g := g;
  }

  ghost constructor D() { // in a ghost context, we only need to know that g's type is nonempty (same as for h all along)
  }
}

type HHH(0)

class GhostableAutoInit {
  var g: HHH
  ghost var h: HHH

  constructor A(g: HHH) {
    this.g := g;
  }

  constructor B() {
  }

  ghost constructor C(g: HHH) {
    this.g := g;
  }

  ghost constructor D() {
  }
}

type JJJ

class GhostablePossibleEmpty {
  var g: JJJ
  ghost var h: JJJ

  constructor A(g: JJJ) {
    this.g := g;
  } // error: h is never assigned

  constructor B() {
  } // error (x2): g and h are never assigned

  ghost constructor C(g: JJJ) {
    this.g := g;
  } // error: h is never assigned

  ghost constructor D() {
  } // error (x2): g and h are never assigned
}
