module M0
{
  class C
  {
    method Foo()
    {
      assume true;
    }
  }
}


module M1 refines M0
{
  class C
  {
    method Foo()
    {
      ...;
      assert false;
    }
  }
}
