// RUN: %exits-with 2 %resolve --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Base extends object {
   var x: int
   function FooSpec(): int
     reads this
   {
     1 / x
   }
   method Foo() returns (r: int)
     ensures r == FooSpec()
   invariant x != 0 // ok, but subclasses cannot then declare an invariant
}

class Ext extends Base {
  var y: int
  invariant y > 0
  method Foo() returns (r: int)
    ensures r == FooSpec()
  {
    r := FooSpec();
  }
}