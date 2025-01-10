// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module A {
  datatype Test = Test(v: nat, w: nat)
  method m(oldTest: Test) {
    var newTest: Test := oldTest[v := 1]; // error: old syntax
  }
}
