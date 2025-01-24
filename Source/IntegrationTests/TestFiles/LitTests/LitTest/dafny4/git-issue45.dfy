// RUN: %testDafnyForEachResolver "%s"


module Library {
}

module Outer {
  import Library

  module Inner {
    import Library
  }
}
