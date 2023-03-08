// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost predicate bad()
{
    forall i :: i in {1}
}
