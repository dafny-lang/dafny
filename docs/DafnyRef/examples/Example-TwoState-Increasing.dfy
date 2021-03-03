twostate predicate Increasing(c: Cell)
  reads c
{
  old(c.data) <= c.data
}
