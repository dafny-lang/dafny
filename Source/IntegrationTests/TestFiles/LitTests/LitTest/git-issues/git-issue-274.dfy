// RUN: %dafny /compile:0 "%s" > "%t"
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

