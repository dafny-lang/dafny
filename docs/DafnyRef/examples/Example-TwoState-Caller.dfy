method Caller(c: Cell)
  modifies c
{
  c.data := c.data + 10;
  label L:
  assert Increasing(c);
  c.data := c.data - 2;
  assert Increasing(c);
  assert !Increasing@L(c);
}
