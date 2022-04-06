// RUN: %dafny /compile:4 /noVerify /compileTarget:go "%s" > "%t"
// RUN: %diff "%t" "%s.expect"

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

method {:run_all_tests} Main()