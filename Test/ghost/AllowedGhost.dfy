// RUN: %baredafny verify %args --print=- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Test()
{
  // Tuples with a single ghost component are allowed and they are compiled to empty tuples.
  var x := (ghost 123);
  var (y) := (ghost 123);
  ghost var z: (ghost int) := (ghost 123);
  var t: (int, ghost int, int) := (20, 2 := 50, ghost 1 := 30);
  var u: () := ();
}
