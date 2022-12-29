// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module P {
  type M
}

module N2 {
  import opened M = P
  trait T {
      var m: M.M
  }
}

