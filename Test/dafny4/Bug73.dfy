// RUN: %exits-with 4 %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma L(m:map<int, int>, r:int, i:int)
    requires i != r;
{
    assert i in m && i != r;
}

lemma L2(m:map<int, int>, r:int, i:int)
    requires i != r;
{
    assert i !in m && i != r;
}
