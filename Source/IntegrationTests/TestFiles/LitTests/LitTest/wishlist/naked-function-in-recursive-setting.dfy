// RUN: %exits-with 2 %verify --show-hints "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function fact(n: int): int
  requires n >= 0
{
  if n == 0 then
    1
  else (
    assert fact.requires(n-1); //WISH
    n * fact(n-1)
  )
}
