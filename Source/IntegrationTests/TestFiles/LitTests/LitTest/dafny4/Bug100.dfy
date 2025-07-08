// RUN: %verify --relax-definite-assignment --allow-axioms "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma lemma_ensures(x:int, RefineInt:int->int)
    requires forall y :: RefineInt.requires(y)
    ensures forall y :: RefineInt(y) + x == RefineInt(x) + y

ghost function Identity(z:int) : int

lemma test()
{
    var v,w:int;
    lemma_ensures(w, Identity);
    //var RefineInt := Identity;
    //assert RefineInt(v) == Identity(v);
    assert Identity(v) + w == Identity(w) + v;
}






