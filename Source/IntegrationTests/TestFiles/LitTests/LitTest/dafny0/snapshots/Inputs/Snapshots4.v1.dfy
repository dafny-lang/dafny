method M()
{
  if (*)
  {
    assert 1 != 1;  // error
  }
  else
  {
    assert 0 == 0;
    assert 2 != 2;  // error
  }
}
