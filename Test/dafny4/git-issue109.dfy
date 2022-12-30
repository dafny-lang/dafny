// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype MyTuple = MyTuple(x:int, y:int)

method M()
  requires forall x :: MyTuple(x,x) != MyTuple(x,x+1)
  requires forall x :: (x,x) != (x,x+1)
{
}


