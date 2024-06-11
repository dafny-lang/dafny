// RUN: %testDafnyForEachResolver "%s"


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



