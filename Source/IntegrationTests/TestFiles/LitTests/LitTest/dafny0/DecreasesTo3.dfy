// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M1() {
  assert (1 decreases to 0) && (0 decreases to 1);
}

method M2() {
  assert (0 decreases to 1);
}
