// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate {:opaque} p(i:int)
{
  i == 3
}

predicate {:opaque} q(x:int)
  requires p(x)
  ensures  p(x)
{
  true
}

lemma L(x:int)
  requires p(x)
{
  reveal_q();
  assert q(x);
  assert x == 3; // succeeds; should fail
}
