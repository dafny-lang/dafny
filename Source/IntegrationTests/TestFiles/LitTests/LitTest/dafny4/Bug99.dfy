// RUN: %testDafnyForEachResolver "%s"


ghost predicate P(e:int, p:int) { true }
ghost predicate Q(i:int, t:int)

lemma Tester(x:int)
{
    assert forall i :: Q(i, x) ==> (forall p {:trigger P(i, p)} :: P(i, p));

}
