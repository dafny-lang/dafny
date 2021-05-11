// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype Nat = x | 0 <= x

method M(N: Nat) {
  var s := 0;
  for i := N downto 0
    invariant s == N * (N + 1) / 2 - i * (i + 1) / 2
  {
    s := s + i;
  }
  for i := 0 to N
    invariant s == N * (N + 1) / 2 - i * (i + 1) / 2
  {
    s := s - i;
  }
  assert s == 0;
}
