// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs /Main:A.B.Main "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js /Main:A.B.Main "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go /Main:A.B.Main "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js /Main:A.B.Main "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=cs /Main:A.C.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js /Main:A.C.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go /Main:A.C.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java /Main:A.C.Test "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  class B {
    method Main() { print "Main\n"; }
  }
  class C {
    method Test() { print "Test\n"; }
  }
}

