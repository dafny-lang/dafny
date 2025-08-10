// RUN: %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Base extends object {
   var x: int
   function FooSpec(): int
     reads this
   method Foo() returns (r: int)
     ensures r == FooSpec()
   invariant x != 0
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

trait Base2 extends object {
  var x: int
  function FooSpec(): int
    reads this
  {
    1 / x
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
  b.x := 1; // checks trait invariant
  e.x := 1; // checks inherited invariant
  e.y := 1; // checks derived invariant
}

method Upcast2(e: Ext2)
  modifies e
{
  var b := e as Base2;
  b.x := 10; // checks original invariant
  e.x := 2; // checks derived invariant
}