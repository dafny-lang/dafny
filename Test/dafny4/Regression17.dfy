// RUN: %exits-with 2 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype nt = int

method Test(x: int)
{
  var y := map[x := nt];  // error (but should not cause a crash): nt is a type
}
