// RUN: %exits-with 4 %verify --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(x: int)

function FirstAssertNotProved(): (i: int)
  ensures P(i)
{
  assert rule2: P(12) by { // error: cannot be verified here
  }
  assert P(12) by {
    reveal rule2;
  }
  12
}

function BothAssertNotProved(): (i: int)
  ensures P(i)
{
  assert rule2: P(12) by { // error: cannot be verified here
  }
  assert P(12) by { // error: cannot be verified here
  }
  12
}

function FirstAssertNotProvedBecauseRequiresNotRevealed(): (i: int)
  requires rule: P(12)
  ensures P(i)
{
  assert rule2: P(12) by { // error: cannot be verified here
  }
  assert P(12) by {
    reveal rule2;
  }
  12
}



function SecondAssertNotProvedBecauseAssertNotRevealed(): (i: int)
  requires rule: P(12)
  ensures P(i)
{
  assert rule2: P(12) by {
    reveal rule;
  }
  assert P(12) by { // error: cannot be verified here
  }
  12
}

function EverythingVerifies(): (i: int)
  requires rule: P(12)
  ensures P(i)
{
  assert rule2: P(12) by {
    reveal rule;
  }
  assert P(12) by {
    reveal rule2;
  }
  12
}

least predicate ShouldNotWork(): (y: bool)
  requires rule: P(12)
{
  assert P(12) by { // Error, cannot prove this
  }
  true
}

least predicate ShouldWork(): (y: bool)
  requires rule: P(12)
{
  assert P(12) by {
    reveal rule;
  }
  true
}