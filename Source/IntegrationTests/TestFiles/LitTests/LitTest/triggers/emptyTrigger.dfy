// RUN: ! %verify "%s" > "%t"
// RUN: ! %run "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method M() {
  assert exists z :: z <= 3;
  assert exists z {:trigger} :: z <= 3;
  assert true;
}
