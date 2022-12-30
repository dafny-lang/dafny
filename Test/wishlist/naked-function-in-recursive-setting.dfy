// RUN: %exits-with 4 %baredafny verify %args --print-tooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function fact(n: int): int
  requires n >= 0
{
  if n == 0 then
    1
  else (
    assert fact.requires(n-1); //WISH
    n * fact(n-1)
  )
}
