// NONUNIFORM: Multiple test scenarios (could be split)
// RUN: %verify "%s" > "%t"
// RUN: %run --no-verify --target cs /Main:A.B.Main "%s" >> "%t"
// RUN: %run --no-verify --target js /Main:A.B.Main "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 --target go /Main:A.B.Main "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 --target js /Main:A.B.Main "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 --target cs /Main:A.C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 --target js /Main:A.C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 --target go /Main:A.C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 --target java /Main:A.C.Test "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  class B {
    method Main() { print "Main\n"; }
  }
  class C {
    method Test() { print "Test\n"; }
  }
}

