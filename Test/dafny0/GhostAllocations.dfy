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
