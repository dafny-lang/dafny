method M()
{
  N();
  assert false;
}

method N()
  ensures P();

predicate P()
  ensures P() == Q();

predicate Q()
  ensures Q() == R();

predicate R()
{
  false
}
