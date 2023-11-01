// RUN: %testDafnyForEachResolver "%s"


module M0.M1.Base {}

module M0.M2 {
  import M1.Base

  module Derived refines Base {
  }
}
