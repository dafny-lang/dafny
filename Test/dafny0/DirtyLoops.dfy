// RUN: %dafny /compile:0 /dprint:"%t.dprint.dfy" "%s" > "%t"; %dafny /noVerify /compile:1 "%t.dprint.dfy" >> "%t"
// RUN: %diff "%s.expect" "%t"

method M0(S: set<int>) {
  forall s | s in S ensures s < 0;
}

method M1(x: int)
{
  var i := x;
  while (0 < i)
    invariant i <= x;
}

method M2(x: int)
{
  var i := x;
  while (0 < i)
    invariant i <= x;
    decreases i;
}
