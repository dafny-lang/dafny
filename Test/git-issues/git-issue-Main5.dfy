// UNSUPPORTED: *
// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs /Main:A.T.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js /Main:A.T.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go /Main:A.T.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java /Main:A.T.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs /Main:A.D.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js /Main:A.D.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go /Main:A.D.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java /Main:A.D.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs /Main:A.C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js /Main:A.C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go /Main:A.C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java /Main:A.C.Test "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  trait T {
    static method Test() { print "Test1\n"; }
  }
  datatype D = D1 | D2 {
    static method Test() { print "Test2\n"; }
  }
  codatatype C = C1 {
    static method Test() { print "Test3\n"; }
  }
}

