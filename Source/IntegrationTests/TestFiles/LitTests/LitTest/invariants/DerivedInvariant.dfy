trait Base {
   var x: int
   function FooSpec(): int
     reads this
   method Foo() returns (r: int)
     ensures r == FooSpec()
   //invariant x != 0 // ok, but subclasses cannot then declare an invariant
}

class Ext extends Base {
  var y: int
  invariant y != 0 // note: invariant can't refer to x
  function FooSpec(): int
    reads this
  {
    1 / y
  }
  method Foo() returns (r: int)
    ensures r == FooSpec()
  {
    r := FooSpec();
  }
}

method Upcast(e: Ext)
  modifies e
{
  var b := e as Base;
  b.x := 0; // no problem;
  e.y := 1; // checks invariant, no problem
}