method RedundantAssumeMethod(n: int)
{
    // either one or the other assumption shouldn't be covered
    assume n > 4;
    assume n > 3;
    assert n > 1;
}

method ContradictoryAssumeMethod(n: int)
{
    assume n > 0;
    assume n < 0;
    assume n == 5; // shouldn't be covered
    assert n < 10; // shouldn't be covered
}
