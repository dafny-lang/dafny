// RUN: %exits-with 2 %dafny /compile:0 /functionSyntax:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Cell {
  ghost var data: int
}

method M(cc: Cell)
  ensures false
{
  var f: () ~> set<Cell> :=
    ()
      reads set c: Cell | c in {c} // error: depends on the allocation state
    => set c: Cell | c.data == 17; // error: depends on the allocation state

  var s := f();
  var d := P(f);
}

ghost method P(f: () ~> set<Cell>) returns (d: Cell)
  requires f.requires()
  ensures f() == old(f())
  ensures d !in f() && d.data == 17
{
  var s := f();

  // The following creates and returns a Cell
  //  - that's previously not in f(), and
  //  - that now has .data equalling 17
  d := new Cell;
  assert d !in s;
  d.data := 17;

  // Since f is presumed not to depend on the allocation state, we can
  // prove the following:
  var t := f();
  assert s == t;
}
