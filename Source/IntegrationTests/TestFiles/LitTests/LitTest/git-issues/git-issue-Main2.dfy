// RUN: %verify "%s" > "%t"
// RUN: %exits-with 3 %run --no-verify --target cs "%s" >> "%t"
// RUN: %exits-with 3 %run --no-verify --target js "%s" >> "%t"
// RUN: %exits-with 3 %run --no-verify --target go "%s" >> "%t"
// RUN: %exits-with 3 %run --no-verify --target java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  module AA {
    method {:main} Main() {}
  }
}

module B {
  class C {
    static method {:main} Main() {}
  }
}

method Main() {}
