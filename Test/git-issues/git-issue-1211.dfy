// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function apply<T,U>(op: T --> U): ()
{
  ()
}

datatype D = O | LD(c: D, thunk: () -> D)
{
  
  function e(d: D): ()
  {
      apply((x: D) requires x.LD? => x.(c := d))
  }
}



