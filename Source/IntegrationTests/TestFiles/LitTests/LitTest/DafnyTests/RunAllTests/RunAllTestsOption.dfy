// RUN: %verify "%s" > "%t"
// RUN: %translate cs %trargs %s --include-runtime --include-test-runner --no-verify --output %S/Output/manual/program.cs >> "%t"
// RUN: ! dotnet run -v q --property WarningLevel=0 --project %S/RunAllTests.csproj >> "%t"
// RUN: ! %baredafny test %args --no-verify --target:cs "%s" >> "%t"
// RUN: ! %baredafny test %args --no-verify --target:java "%s" >> "%t"
// RUN: ! %baredafny test %args --no-verify --target:go "%s" >> "%t"
// RUN: ! %baredafny test %args --no-verify --target:js "%s" >> "%t"
// RUN: ! %baredafny test %args --no-verify --target:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t" 

include "../../exceptions/VoidOutcomeDt.dfy"
include "../../exceptions/NatOutcomeDt.dfy"

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
