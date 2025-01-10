// RUN: %testDafnyForEachResolver "%s"


module M {
  export
    provides
      Opened,
      f

  module Opened {
    type T = int
  }

  ghost function f(x: Opened.T): int {
    5
  }
}
