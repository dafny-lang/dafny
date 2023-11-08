// RUN: %testDafnyForEachResolver "%s"


module B {
  datatype Test = Test(v: nat, w: nat)
  method m(oldTest: Test) {
    var newTest2: Test := oldTest.(v := 1, w := 2);
  }
}
