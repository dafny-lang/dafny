// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T {
  opaque predicate True() { true }
}

class C extends T {}

method TestOpaque(c: C) {
  assert c.True(); // error: True is opaque and hasn't been revealed
}

method TestRevealed(c: C) {
  reveal c.True(); // test that True can be revealed
  assert c.True(); // now, the assertion goes through
}
