// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost predicate {:opaque} ValidRegs()
{
    forall i:int {:nowarn}:: true
}

ghost predicate mypredicate()
    requires ValidRegs()

lemma mylemma()
{
    assume mypredicate();
}

