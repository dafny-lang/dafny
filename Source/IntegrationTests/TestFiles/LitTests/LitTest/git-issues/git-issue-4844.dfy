// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Ooops()
  ensures false
{
  var x := new O();
  assert AllocationSoundness(x);
}

class O {
  var x: int
  constructor() {}
}

twostate predicate AllocationSoundness(o: O)
  ensures old(allocated(o))
{ true }
