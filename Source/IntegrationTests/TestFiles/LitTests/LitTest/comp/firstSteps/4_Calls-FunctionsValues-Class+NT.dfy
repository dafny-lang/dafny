// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment
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
    function F(): int { x }
    static function G(): int { 3 }
  }

  newtype NT = x | 0 <= x < 15 {
    function F(): int { this as int }
    static function G(): int { 3 }
  }
}

method Main()
{
  FunctionValues.Test();
}
