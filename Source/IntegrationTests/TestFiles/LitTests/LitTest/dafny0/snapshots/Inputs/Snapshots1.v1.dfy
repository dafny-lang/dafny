method M()
{
  N();
  assert false;  // error
}

method N()
  ensures P();

predicate P()
{
  true
}
