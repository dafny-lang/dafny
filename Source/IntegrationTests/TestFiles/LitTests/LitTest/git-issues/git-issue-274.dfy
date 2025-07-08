// RUN: %testDafnyForEachResolver "%s"


module P {
  type M
}

module N2 {
  import opened M = P
  trait T extends object {
    var m: M.M
  }
}
