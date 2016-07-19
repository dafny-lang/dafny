module M0
{
  class C
  {
    method Foo()
      requires true;
    {
    }
  }
}


module M1 refines M0
{
  class C
  {
    method Foo...
    {
      assert false;
    }
  }
}
