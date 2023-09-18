// RUN: ! %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma test()
{
    match 0
    case 0 =>
      forall i: nat ensures match true {}
}