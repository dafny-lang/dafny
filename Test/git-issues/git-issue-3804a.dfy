// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(x: int)

function {:rlimit 1000} {:vcs_split_on_every_assert} DoesNotPass(): (i: int)
  ensures P(i)
  requires rule: forall i | i % 2 == 0 :: P(i)
{
  assert rule: forall i | i % 4 == 0 :: P(i); // Error here, rule is dominated.
  12
}