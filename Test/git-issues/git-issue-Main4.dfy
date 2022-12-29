// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs /Main:A.AA.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js /Main:A.AA.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go /Main:A.AA.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java /Main:A.AA.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs /Main:B.C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js /Main:B.C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go /Main:B.C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java /Main:B.C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs /Main:B.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js /Main:B.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go /Main:B.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java /Main:B.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs /Main:Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js /Main:Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go /Main:Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java /Main:Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs /Main:C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js /Main:C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go /Main:C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java /Main:C.Test "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /compileTarget:cs /Main:X "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /compileTarget:js /Main:X "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /compileTarget:go /Main:X "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /compileTarget:java /Main:X "%s" >> "%t"

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
