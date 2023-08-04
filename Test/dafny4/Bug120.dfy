// RUN: %dafny /compile:0 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function G(n: nat): nat
{
  if n == 0 then 5 else G(n-1)
}

method Test() {
  assert G(10) == 5;
}