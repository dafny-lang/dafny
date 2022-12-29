// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function{:opaque} MapSetToSet<X(!new), Y>(xs:set<X>, f:X~>Y):set<Y>
//function MapSetToSet<X, Y>(xs:set<X>, f:X->Y):set<Y>
  reads f.reads;
  requires forall x :: f.requires(x);
{
  set x | x in xs :: f(x)
}
