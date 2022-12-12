// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  export provides T
  type T = bool
}

module B {
  import A
  method Test() {
     var e : A.T;
     var f := e == false; // error
  }
}

module C {
  module D {
     export provides T
     type T = bool
  }

  method Test() {
     var e : D.T;
     var f := e == false; // error
  }

}


module E { // error (implicit export E causes duplicate toplevel error)
  export E provides T
  export reveals T // error

  type T = bool

}
