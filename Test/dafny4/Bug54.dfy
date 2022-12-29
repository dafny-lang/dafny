// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate G<X(!new)>(f:X~>bool)
  reads f.reads;
  requires forall x :: f.requires(x) && f(x);
{
  true
}

predicate H()
{
  G((x:int) => true)
}

predicate P1<X>(m:map<X,bool>)
  requires forall x :: x in m ==> m[x];
{
  true
}

predicate P2(m:map<int,bool>)
  requires forall x :: x in m ==> m[x];
{
  P1(map x:int | x in m :: true)
}
