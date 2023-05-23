// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(x: int)

function DoesNotPass(x: bool): (i: int)
  ensures P(i)
  requires rule: P(12)
{
  assert rule: P(12); // Error here, rule is dominated.
  assert rule2: P(12);
  if x then
    assert rule2: P(12); // Error here, rule2 is dominated.
    12
  else
    12
}