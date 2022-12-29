// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs /Main:A.B.Main "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js /Main:A.B.Main "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go /Main:A.B.Main "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js /Main:A.B.Main "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs /Main:A.C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js /Main:A.C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go /Main:A.C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java /Main:A.C.Test "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  class B {
    method Main() { print "Main\n"; }
  }
  class C {
    method Test() { print "Test\n"; }
  }
}

