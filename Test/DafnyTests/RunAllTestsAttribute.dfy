// RUN: %dafny /compile:4 /noVerify "%s" > "%t"
// RUN: %diff "%t" "%s.expect"

method {:test} Passing1() {
  expect 2 == 2;
}

method {:test} Passing2() {
  expect 2 + 2 == 4;
}

method {:test} Failing() {
  expect 2 + 2 == 5;
}

method {:run_all_tests} Main()