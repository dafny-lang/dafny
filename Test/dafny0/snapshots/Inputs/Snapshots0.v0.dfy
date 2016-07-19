method foo()
{
  bar();
  assert false;
}

method bar()
  ensures false;
