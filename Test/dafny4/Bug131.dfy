// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Cell {
  method Test(c: Cell) {
    assert c.F();
  }
}

predicate F()

