// RUN: %exits-with 4 %verify --type-system-refresh --check-invariants "%s" > "%t"
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
  constructor() {
    x := 0;
    y := 1;
  }
}

method Upcast(e: Ext)
  modifies e
{
  var b := e as Base;
  b.x := 1; // checks trait invariant
  e.y := 1; // checks derived invariant
  if * {
    e.x := 0; // error: checks trait invariant
  } else {
    b.x := 0; // error: checks inherited invariant
  }
}
