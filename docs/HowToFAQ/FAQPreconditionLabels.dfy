method M0(x: int)
  requires x == 0
{
  assert x < 10; // verifies
}

method M1(x: int)
  requires Zero: x == 0
{
  // the following assertion does not verify, because labeled
  // preconditions are hidden
  assert x < 10; // error
}

method M2(x: int)
  requires Zero: x == 0
{
  // by revealing the hidden precondition, the assertion verifies
  reveal Zero;
  assert x < 10; // verifies
}
