// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate bad()
{
    forall i :: i in {1}
}
