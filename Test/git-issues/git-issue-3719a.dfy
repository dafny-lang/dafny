// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost opaque function R(i: int): int {
  i
}

lemma Test() {
  assert 1 == R(1) by {reveal R(); }
  assert 1 == R(1);
}