// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(e:int, p:int) { true }
predicate Q(i:int, t:int)

lemma Tester(x:int)
{
    assert forall i :: Q(i, x) ==> (forall p {:trigger P(i, p)} :: P(i, p));

}
