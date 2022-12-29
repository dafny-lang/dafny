// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function I(f:int->bool):int->bool
    ensures I(f) == f;

predicate G<S>(s:S)

type D<X>
type E

lemma L1<S>(b:int->S)
    requires forall i :: b.reads(i) == {};
    requires forall i :: b.requires(i);
    requires I(j => G(b(j)))(0); // PRECONDITION NOT SATISFIED BY L2

lemma L2(b:int->D<E>)
    requires forall i :: b.reads(i) == {};
    requires forall i :: b.requires(i);
    requires I(j => G(b(j)))(0);
{
    L1(b); // FAILS TO SATISFY L1's PRECONDITION
}
