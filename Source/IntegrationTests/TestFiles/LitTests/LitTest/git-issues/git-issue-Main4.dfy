// NONUNIFORM: Multiple test scenarios (could be split)
// RUN: %verify "%s" > "%t"
// RUN: %run --no-verify --target cs /Main:A.AA.Test "%s" >> "%t"
// RUN: %run --no-verify --target js /Main:A.AA.Test "%s" >> "%t"
// RUN: %run --no-verify --target go /Main:A.AA.Test "%s" >> "%t"
// RUN: %run --no-verify --target java /Main:A.AA.Test "%s" >> "%t"
// RUN: %run --no-verify --target cs /Main:B.C.Test "%s" >> "%t"
// RUN: %run --no-verify --target js /Main:B.C.Test "%s" >> "%t"
// RUN: %run --no-verify --target go /Main:B.C.Test "%s" >> "%t"
// RUN: %run --no-verify --target java /Main:B.C.Test "%s" >> "%t"
// RUN: %run --no-verify --target cs /Main:B.Test "%s" >> "%t"
// RUN: %run --no-verify --target js /Main:B.Test "%s" >> "%t"
// RUN: %run --no-verify --target go /Main:B.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 --target java /Main:B.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 --target cs /Main:Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 --target js /Main:Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 --target go /Main:Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 --target java /Main:Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 --target cs /Main:C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 --target js /Main:C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 --target go /Main:C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 --target java /Main:C.Test "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 --target cs /Main:X "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 --target js /Main:X "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 --target go /Main:X "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 --target java /Main:X "%s" >> "%t"

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
