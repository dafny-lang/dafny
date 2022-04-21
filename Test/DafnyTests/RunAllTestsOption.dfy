// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs   /runAllTests:1 "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java /runAllTests:1 "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go   /runAllTests:1 "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js   /runAllTests:1 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t" 

include "../exceptions/VoidOutcomeDt.dfy"
include "../exceptions/NatOutcomeDt.dfy"

method {:test} Passing1() {
  expect 2 == 2;
}

method {:test} Passing2() {
  expect 2 + 2 == 4;
}

method {:test} Failing1() {
  expect 2 + 2 == 5;
}

method {:test} Passing3() {
  expect 2 + 2 == 4;
}

method {:test} Failing2() {
  expect 2 + 2 == 5;
}

module TestModule {
  method {:test} Passing1() {
    expect 2 + 2 == 4;
  }
}

method {:test} FailingReturnValue() returns (result: VoidOutcome) {
  return VoidFailure("Whoopsie");
}
