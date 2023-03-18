// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny -?
// RUN: %baredafny -h
// RUN: %baredafny --help

// Checks unicode symbols
method m1() {
  assert 1 ≠ 2;
  assert 1 ≤ 2;
  assert 2 ≥ 1;
  assert false ⇔ false;
  assert false ⇒ true;
  assert true ⇐ false;
  assert true ∧ true;
  assert true ∨ false;
  assert ¬ false;
  assert ∀ x: int • true;
  assert ∃ x: int • true;
}

