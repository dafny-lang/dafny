// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(x: int)

function {:rlimit 1000} {:vcs_split_on_every_assert} AssertNotProved(): (i: int)
  ensures P(i)
{
  assert rule2: forall i | i % 4 == 0 :: P(i) by {
    //reveal rule;
  }
  assert P(12) by {
    reveal rule2;
  }
  12
}

function {:rlimit 1000} {:vcs_split_on_every_assert} BothAssertNotProved(): (i: int)
  ensures P(i)
{
  assert rule2: forall i | i % 4 == 0 :: P(i) by {
    //reveal rule;
  }
  assert P(12) by {
    //reveal rule2;
  }
  12
}

function {:rlimit 1000} {:vcs_split_on_every_assert} FirstAssertNotProvedBecauseRequiresNotRevealed(): (i: int)
  requires rule: forall i | i % 2 == 0 :: P(i)
  ensures P(i)
{
  assert rule2: forall i | i % 4 == 0 :: P(i) by { // Fails
    //reveal rule;
  }
  assert P(12) by {
    reveal rule2;
  }
  12
}

function {:rlimit 1000} {:vcs_split_on_every_assert} EverythingVerifies(): (i: int)
  ensures P(i)
  requires rule: forall i | i % 2 == 0 :: P(i)
{
  assert rule2: forall i | i % 4 == 0 :: P(i) by {
    reveal rule;
  }
  assert P(12) by {
    reveal rule2;
  }
  12
}