// RUN: %baredafny verify %args "%s" > "%t"

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

// Some chains not tested elsewhere
method m2(s: set<int>) {
  assert 9 == 9 > 8;
  assert 9 == 9 >= 9;
  assert s !! s != true;
  assert true <== true ==> true <== true ==> true;
}