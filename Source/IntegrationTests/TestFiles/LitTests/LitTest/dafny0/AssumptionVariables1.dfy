// RUN: %baredafny verify %args --relax-definite-assignment --boogie=/print:%t.bprint --print="%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method test0(x: int)
{
  ghost var {:assumption} a0: bool;
  ghost var {:assumption} a1: bool, a2: bool, {:assumption} a3: bool;

  assert a0 && a1 && a3;

  a0 := a0 && (0 < x);

  a1 := a1 && true;
}


method test1(x: int)
{
  ghost var {:assumption} a0: bool;

  assert a0;

  a0 := a0 && (0 < x);

  var y := x;

  while (y < 0)
  {
    ghost var {:assumption} a0: bool;

    assert a0;

    a0 := a0 && (0 < y);

    y := y + 1;
  }
}
