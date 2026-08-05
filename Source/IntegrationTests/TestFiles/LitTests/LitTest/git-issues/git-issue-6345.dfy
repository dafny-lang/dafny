// RUN: %testDafnyForEachResolver "%s"

// Regression test: named class constructor inside match case crashed
// because MatchFlattener cloned an AllocateClass with unresolved Path type.

datatype Color = Red | Blue

class C {
  constructor Init(x: int) { }
}

method Test(color: Color) {
  match color
  case Red =>
    var v := new C.Init(165);
  case Blue =>
}

// The same MatchFlattener clone path also reaches AssignSuchThatStmt, whose Bounds list holds a
// null element for a variable no bound was discovered for (BoundedPool.GetBest returns null);
// cloning it dereferenced that element. The constraint has to be one that yields no bound: a
// bare `o == c` gives a discoverable one, so it does not reproduce the crash, while the
// disjunction below does and still verifies.

method AssignSuchThat(b: bool, c: C) returns (r: C) {
  match b
  case true =>
    var o: C :| o == c || o == c;
    r := o;
  case false =>
    r := c;
}
