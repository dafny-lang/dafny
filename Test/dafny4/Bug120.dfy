// RUN: %baredafny verify %args --disable-nonlinear-arithmetic "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function G(n: nat): nat
{
  if n == 0 then 5 else G(n-1)
}

method Test() {
  assert G(10) == 5;
}
