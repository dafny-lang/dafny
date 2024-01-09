// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


newtype nt = int

method Test(x: int)
{
  var y := map[x := nt];  // error (but should not cause a crash): nt is a type
}
