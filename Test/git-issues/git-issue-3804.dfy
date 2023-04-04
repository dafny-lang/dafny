// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(x: int)

function test(): (i: int)
  ensures P(i)
  requires rule: forall i | i % 2 == 0 :: P(i)
{
  assert rule2: forall i | i % 4 == 0 :: P(i) by {
    reveal rule;
  }
  assert P(12) by {
    reveal rule;
  }
  12
}