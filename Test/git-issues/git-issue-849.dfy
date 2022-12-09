// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  datatype Test = Test(v: nat, w: nat)
  method m(oldTest: Test) {
    var newTest: Test := oldTest[v := 1]; // error: old syntax
  }
}
