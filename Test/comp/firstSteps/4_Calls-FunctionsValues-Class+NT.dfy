// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=py "%s" "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
//
// This fragment of comp/Calls.dfy serves to facilitate incremental compiler development.

module FunctionValues {
  method Test() {
    var c := new Class(5);
    var nt: NT := 5;
    ApplyAndPrint(c.F);
    ApplyAndPrint(c.G);
    ApplyAndPrint(nt.F);
    ApplyAndPrint(nt.G);
    print "\n";
    // test variable capture
    var x0, x1, x4, x5 := c.F, c.G, nt.F, nt.G;
    c := new Class(2);
    nt := 2;
    print x0(), " ", x1(), " ", x4(), " ", x5(), "\n";
  }

  method ApplyAndPrint(f: () -> int) {
    print f(), " ";
  }

  class Class {
    const x: int
    constructor (x: int) { this.x := x; }
    function method F(): int { x }
    static function method G(): int { 3 }
  }

  newtype NT = x | 0 <= x < 15 {
    function method F(): int { this as int }
    static function method G(): int { 3 }
  }
}

method Main()
{
  FunctionValues.Test();
}
