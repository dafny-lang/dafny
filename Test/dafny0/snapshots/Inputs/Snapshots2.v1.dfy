method M()
{
  N();
  assert false;  // error
}

method N()
  ensures P();

predicate P()
  ensures P() == Q();

predicate Q()
  ensures Q() == R();

predicate R()
{
  true
}
