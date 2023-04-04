// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(x: int)

function FirstAssertNotProved(): (i: int)
  ensures P(i)
{
  assert rule2: P(12) by {
  }
  assert P(12) by {
    reveal rule2;
  }
  12
}

function BothAssertNotProved(): (i: int)
  ensures P(i)
{
  assert rule2: P(12) by {
  }
  assert P(12) by { // Fails
  }
  12
}

function FirstAssertNotProvedBecauseRequiresNotRevealed(): (i: int)
  requires rule: P(12)
  ensures P(i)
{
  assert rule2: P(12) by {
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
  assert P(12) by {
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