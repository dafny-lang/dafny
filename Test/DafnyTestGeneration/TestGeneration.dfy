// Generating tests:
// RUN: cp %S/TestGeneration.dfy %t.dfy
// RUN: %dafny /definiteAssignment:3 /generateTestMode:Block %t.dfy > %t-tests.dfy
// RUN: %dafny_0 /compileVerbose:1 /compile:0 /spillTargetCode:3 /noVerify "%t-tests.dfy" > "%t"
// RUN: dotnet test -v:q -noLogo %S >> %t || true

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
