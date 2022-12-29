// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function KeepDoin'It(x: nat): nat
  decreases x;
{
  KeepDoin'It(x + 1)
}

lemma Test(r: nat)
{
  assert KeepDoin'It(20) == r;
}

