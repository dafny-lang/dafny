// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


class C {
  var x:nat
  twostate predicate p() { unchanged(this) }
  method bad() modifies this ensures false {
    assert p();
    x := x+1;
    assert p();
  }
}
