// RUN: %verify "%s" > "%t"
// RUN: %exits-with 3 %run --no-verify --target cs "%s" >> "%t"
// RUN: %exits-with 3 %run --no-verify --target js "%s" >> "%t"
// RUN: %exits-with 3 %run --no-verify --target go "%s" >> "%t"
// RUN: %exits-with 3 %run --no-verify --target java "%s" >> "%t"
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
