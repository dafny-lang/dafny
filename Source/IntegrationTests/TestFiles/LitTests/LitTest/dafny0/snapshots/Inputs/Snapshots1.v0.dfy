method M()
{
  N();
  assert false;
}

method N()
  ensures P();

predicate P()
{
  false
}
