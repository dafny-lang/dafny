// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function KeepDoin'It(x: nat): nat
  decreases x;
{
  KeepDoin'It(x + 1)
}

lemma Test(r: nat)
{
  assert KeepDoin'It(20) == r;
}

