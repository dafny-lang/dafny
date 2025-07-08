// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


function F(x: int, w: int): (int, int)
  requires x < 100

function G(m: int): int
  requires 0 <= m

method Test(y: int, n: nat)
{
  // In a previous version of Dafny, the following line had caused two
  // error messages of the precondition violation.
  var (a, b) := F(y, G(n));  // error: precondition violation
}
