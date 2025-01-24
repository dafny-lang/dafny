// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


class Cell {
  method Test(c: Cell) {
    assert c.F();
  }
}

ghost predicate F()

