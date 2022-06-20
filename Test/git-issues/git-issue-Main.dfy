// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny_0 /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny_0 /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny_0 /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny_0 /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  module AA {
    method Main() {}
  }
}

module B {
  class C {
    static method Main() {}
  }
}

method Main() {}
