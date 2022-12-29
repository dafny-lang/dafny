// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function method apply<T,U>(op: T --> U): ()
{
  ()
}

datatype D = O | LD(c: D, thunk: () -> D)
{
  
  function method e(d: D): ()
  {
      apply((x: D) requires x.LD? => x.(c := d))
  }
}



