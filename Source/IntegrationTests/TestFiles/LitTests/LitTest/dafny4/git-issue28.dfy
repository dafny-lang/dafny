// RUN: %testDafnyForEachResolver "%s"


lemma mylemma()
{
    var shift:int := 1;
    assume (1 as bv32 << shift) as int == 2;
    assert (1 as bv32 << 1) as int == 2;
}

