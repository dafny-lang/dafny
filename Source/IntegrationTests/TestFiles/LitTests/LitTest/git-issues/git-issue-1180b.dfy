// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// verification errors

module StartingFromOpaqueType {
  abstract module A {
    type Ty {
      const c: nat
      function F(x: nat): nat
        requires x != 7
        ensures F(x) == c
      method M(x: nat) returns (r: nat)
        requires x != 9
        ensures r == x
    }
    method Caller(t: Ty, x: int) {
      var c := t.c;
      if c != 9 {
        var r := t.M(t.c);
        var u := t.F(2 * c);
        assert r == u;
      }
    }
  }
  module OpaqueType refines A {
    type Ty ... {
      function F(x: nat): nat { x } // error: postcondition violation
      method M(x: nat) returns (r: nat) { r := c; } // error: postcondition violation
    }
  }
  module Datatype refines A {
    datatype Ty = Make(w: int) {
      function F(x: nat): nat { x } // error: postcondition violation
      method M(x: nat) returns (r: nat) { r := c; } // error: postcondition violation
    }
  }
  module Codatatype refines A {
    codatatype Ty = Make(w: int) {
      function F(x: nat): nat { x } // error: postcondition violation
      method M(x: nat) returns (r: nat) { r := c; } // error: postcondition violation
    }
  }
  module Newtype refines A {
    newtype Ty = int {
      function F(x: nat): nat { x } // error: postcondition violation
      method M(x: nat) returns (r: nat) { r := c; } // error: postcondition violation
    }
  }
  module Class refines A {
    class Ty {
      constructor () {
        c := 65;
      }
      var q: int
      function F(x: nat): nat { x } // error: postcondition violation
      method M(x: nat) returns (r: nat) { r := c; } // error: postcondition violation
    }
  }
  module Trait refines A {
    trait Ty extends object {
      var q: int
      function F(x: nat): nat { x } // error: postcondition violation
      method M(x: nat) returns (r: nat) { r := c; } // error: postcondition violation
    }
  }
}

module StartingFromDatatype {
  abstract module A {
    datatype Ty = Make(w: int) {
      const c: nat
      function F(x: nat): nat
        requires x != 7
        ensures F(x) == c
      method M(x: nat) returns (r: nat)
        requires x != 9
        ensures r == x
    }
  }
  module Datatype refines A {
    datatype Ty ... {
      function F(x: nat): nat { x } // error: postcondition violation
      method M(x: nat) returns (r: nat) { r := c; } // error: postcondition violation
    }
  }
}

module StartingFromNewtype {
  abstract module A {
    newtype Ty = int {
      const c: nat
      function F(x: nat): nat
        requires x != 7
        ensures F(x) == c
      method M(x: nat) returns (r: nat)
        requires x != 9
        ensures r == x
    }
  }
  module Newtype refines A {
    newtype Ty ... {
      function F(x: nat): nat { x } // error: postcondition violation
      method M(x: nat) returns (r: nat) { r := c; } // error: postcondition violation
    }
  }
}

module StartingFromClass {
  abstract module A {
    class Ty {
      const c: nat
      function F(x: nat): nat
        requires x != 7
        ensures F(x) == c
      method M(x: nat) returns (r: nat)
        requires x != 9
        ensures r == x
    }
  }
  module Newtype refines A {
    class Ty ... {
      function F(x: nat): nat { x } // error: postcondition violation
      method M(x: nat) returns (r: nat) { r := c; } // error: postcondition violation
    }
  }
}

module StartingFromTrait {
  abstract module A {
    trait Ty {
      const c: nat
      function F(x: nat): nat
        requires x != 7
        ensures F(x) == c
      method M(x: nat) returns (r: nat)
        requires x != 9
        ensures r == x
    }
  }
  module Newtype refines A {
    trait Ty ... {
      function F(x: nat): nat { x } // error: postcondition violation
      method M(x: nat) returns (r: nat) { r := c; } // error: postcondition violation
    }
  }
}
