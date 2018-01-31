// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Imported from bug 76. LitInt would be triggered on, causing matching failures.

predicate P(x:int, y:int)

lemma L1(x:int, y:int)
    requires y == 2;
    requires forall i :: P(i, 3);
{
    assert P(x, y + 1);
}

lemma L2(x:int, y:int)
    requires y == 2;
    requires forall i {:trigger P(i, 3)} :: P(i, 3);
{
    assert P(x, y + 1);
}

lemma L3(x:int, y:int)
    requires y == 2;
    requires forall i :: P(i, 3);
{
    var dummy := 3;
    assert P(x, y + 1);
}

lemma L4(x:int, y:int)
    requires y == 2;
    requires forall i, j :: j == 3 ==> P(i, j);
{
    assert P(x, y + 1);
}

// Local Variables:
// dafny-prover-local-args: ("/autoTriggers:1")
// End:
