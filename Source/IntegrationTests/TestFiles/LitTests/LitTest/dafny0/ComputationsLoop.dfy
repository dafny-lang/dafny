// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


ghost function KeepDoin'It(x: nat): nat
  decreases x
{
  KeepDoin'It(x + 1)
}

lemma Test(r: nat)
{
  assert KeepDoin'It(20) == r;
}

