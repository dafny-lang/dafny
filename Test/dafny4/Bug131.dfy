// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Cell {
  method Test(c: Cell) {
    assert c.F();
  }
}

predicate F()

