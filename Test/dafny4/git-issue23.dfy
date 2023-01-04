// RUN: %exits-with 4 %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate {:opaque} ValidRegs()
{
    forall i:int {:nowarn}:: true
}

predicate mypredicate()
    requires ValidRegs()

lemma mylemma()
{
    assume mypredicate();
}

