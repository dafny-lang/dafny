// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma test()
{
    match 0
    case 0 =>
      forall i: nat ensures match true {}
}

datatype T = X
lemma Crash(e: T)
{
  match e
  case X =>
    assert forall k :: match k == true case p => p;
}