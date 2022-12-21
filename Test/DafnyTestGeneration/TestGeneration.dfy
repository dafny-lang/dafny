// Generating tests:
// RUN: cp %S/TestGeneration.dfy %t.dfy
// RUN: %baredafny generate-tests %args Block %t.dfy > %t-tests.dfy
// RUN: %baredafny translate %args --include-runtime --compile-verbose --no-verify "%t-tests.dfy" > "%t" 
// RUN: dotnet test -v:q %S >> %t

// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: .*Passed!  - Failed:     0, Passed:     3, Skipped:     0, Total:     3*

module M {
  class Value {
    var v:int;
  }
  method compareToZero(v:Value) returns (i:int) {
    if (v.v == 0) {
      return 0;
    } else if (v.v > 0) {
      return 1;
    }
    return -1;
  }
}
