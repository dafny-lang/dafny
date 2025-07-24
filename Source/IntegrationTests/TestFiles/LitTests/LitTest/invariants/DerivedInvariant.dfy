// RUN: %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Base extends object {
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
    assert this.invariant(); 1 / y
  }
  method Foo() returns (r: int)
    ensures r == FooSpec()
  {
    r := FooSpec();
  }
}

trait Base2 extends object {
  var x: int
  function FooSpec(): int
    reads this
  {
    assert this.invariant(); 1 / x
  }
  method Foo() returns (r: int)
    ensures r == FooSpec()
  invariant x != 0
}

class Ext2 extends Base2 {
  method Foo() returns (r: int)
    ensures r == FooSpec()
  {
    r := 1 / x;
  }
}

method Upcast(e: Ext)
  modifies e
{
  var b := e as Base;
  b.x := 0; // no problem;
  e.y := 1; // checks invariant, no problem
}

method Upcast2(e: Ext2)
  modifies e
{
  var b := e as Base2;
  b.x := 10; // checks invariant
  e.x := 2; // checks invariant
}