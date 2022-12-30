// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs /Main:A.AA.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js /Main:A.AA.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go /Main:A.AA.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java /Main:A.AA.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=cs /Main:B.C.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js /Main:B.C.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go /Main:B.C.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java /Main:B.C.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=cs /Main:B.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js /Main:B.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go /Main:B.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java /Main:B.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=cs /Main:Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js /Main:Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go /Main:Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java /Main:Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=cs /Main:C.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js /Main:C.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go /Main:C.Test "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java /Main:C.Test "%s" >> "%t"
// RUN: %exits-with 3 %baredafny run %args --no-verify --target=cs /Main:X "%s" >> "%t"
// RUN: %exits-with 3 %baredafny run %args --no-verify --target=js /Main:X "%s" >> "%t"
// RUN: %exits-with 3 %baredafny run %args --no-verify --target=go /Main:X "%s" >> "%t"
// RUN: %exits-with 3 %baredafny run %args --no-verify --target=java /Main:X "%s" >> "%t"

module A {
  module AA {
    method Test() { print "Test1\n"; }
  }
}

module B {
  class C {
    static method Test() { print "Test2\n"; }
  }
  method Test() { print "Test3\n"; }
}

method Test() { print "Test4\n"; }

class C {
  static method Test() { print "Test5\n"; }
}
