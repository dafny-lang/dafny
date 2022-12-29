// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This tests all sorts of combinations of duplicate declarations

module Z {}
module A {
  export E1 reveals *
  export E2 reveals *
  export E3 reveals *
  export E4 reveals *
  export E5 reveals *
  export E6 reveals *
  module E1 {}
  import E2 = Z
  type T3
  const E4 := 0
  method E5() {}
  class E6 {}
}

module B1 {
  module E1 {}
  module E3 {}
  module E4 {}
  module E5 {}
  module E6 {}
  type T3
  const E4 := 0  // error
  method E5() {} // error
  class E6 {} // error
}

module C {
  type T1
  type T2
  type T3
  type T4 = int
  type T1 // error
  const T2 := 0 // error
  method T3() {} // error
  class T4 {} // error
}

module D {
  const T2 := 0
  const T3 := 0
  class T4 {}
  const T2 := 0 // error
  method T3() {} // error
  method T3() {} // error
  const T4 := 0 // error
  method T4() {} // error
  class T4 {} // error
}

