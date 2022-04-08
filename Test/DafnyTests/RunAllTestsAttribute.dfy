// RUN: %dafny /runAllTests:1 /compile:3 /compileTarget:go "%s" > "%t"
// RUN: %diff "%t" "%s.expect"

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
