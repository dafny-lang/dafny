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
