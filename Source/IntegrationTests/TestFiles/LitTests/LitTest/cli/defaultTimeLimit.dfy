// RUN: ! %baredafny verify --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() {
  // Assert something that takes a long time to verify
  assert Ack(4, 2) == 1;
}

function Ack(m: nat, n: nat): nat
{
  if m == 0 then
    n + 1
  else if n == 0 then
    Ack(m - 1, 1)
  else
    Ack(m - 1, Ack(m, n - 1))
}