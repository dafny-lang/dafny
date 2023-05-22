// RUN: %exits-with 2 %run "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
module M {
  const a: int
  const b: int
  export Z reveals a, provides b
}

module P {
  const c = 5
  class C {
    var x = 5
  }
}
