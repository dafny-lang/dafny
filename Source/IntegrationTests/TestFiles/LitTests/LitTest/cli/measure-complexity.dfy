// RUN: %exits-with 4 %baredafny measure-complexity --isolate-assertions --worst-amount 100 "%s" > %t.raw
// RUN: %sed 's#consumed \d+ resources#consumed <redacted> resources#g' %t.raw > %t
// RUN: %diff "%s.expect" "%t"
method Foo() {
  assert Ack(0,0) == 10;
  assert Ack(1,3) == 10;
  assert Ack(3,3) == 10;
  assert Ack(3,4) == 10;
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