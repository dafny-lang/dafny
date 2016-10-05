// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate bad()
{
    forall i :: i in {1}
}
