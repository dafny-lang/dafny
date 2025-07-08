// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment
//
// This fragment of comp/Calls.dfy serves to facilitate incremental compiler development.

module FunctionValues {
  method Test() {
    var color := Red;
    ApplyAndPrint(color.F);
    ApplyAndPrint(color.G);
    print "\n";
    // test variable capture
    var x2, x3 := color.F, color.G;
    color := Blue;
    print x2(), " ", x3(), "\n";
  }

  method ApplyAndPrint(f: () -> int) {
    print f(), " ";
  }

  datatype Color = Red | Green | Blue {
    function F(): int { if this == Red then 5 else 2 }
    static function G(): int { 3 }
  }
}

method Main()
{
  FunctionValues.Test();
}
