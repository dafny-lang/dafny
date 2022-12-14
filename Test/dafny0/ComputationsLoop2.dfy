// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function KeepDoin'It(x: nat): nat
{
  KeepDoin'ItToo(x + 1)
}

function KeepDoin'ItToo(x: nat): nat
{
  KeepDoin'It(x + 1)
}

lemma Test(r: nat)
{
  assert KeepDoin'It(20) == r;
}
