// RUN: %verify --warn-shadowing --allow-warnings "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma L(x:int)
{
    var x := 2;
}

lemma {:warnShadowing false} L1(x:int)
{
    var x := 2;
}
