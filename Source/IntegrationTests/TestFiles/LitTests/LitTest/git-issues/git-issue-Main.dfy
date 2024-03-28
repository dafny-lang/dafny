// RUN: %verify "%s" > "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 --target cs "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 --target js "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 --target go "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 --target java "%s" >> "%t"
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
