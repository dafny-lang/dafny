method foo()
{
  bar();
  assert false;  // error
}

method bar()
  ensures true;
