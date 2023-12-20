// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


ghost predicate P(i:int) { true }

lemma Tester()
{
//    forall i ensures false ==> P(i) {}
    forall i ensures P(i) <== false {}
    assert forall i :: P(i) ==> false;
    assert P(0);
    assert false;
}






