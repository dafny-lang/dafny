// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module P {
  class B {
    var z: int = 5
  }
  class C {
    var s
  }
  class D {
    var t := 6
  }
}
