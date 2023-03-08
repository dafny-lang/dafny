// RUN: %exits-with 2 %dafny /compile:0 /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// resolution errors

module BadRefiningIndications {
  type Opaque ... // error: uses ... but there's nothing to refine
  type Opaque' ... { } // error: uses ... but there's nothing to refine
  datatype Datatype ... // error: uses ... but there's nothing to refine
  codatatype Codatatype ... // error: uses ... but there's nothing to refine
  newtype Newtype ... // error: uses ... but there's nothing to refine
  class Class ... { } // error: uses ... but there's nothing to refine
  trait Trait ... { } // error: uses ... but there's nothing to refine
}

module EmptyRefinementParent { }

module MoreBadRefiningIndications refines EmptyRefinementParent {
  type Opaque ... // error: uses ... but there's nothing to refine
  type Opaque' ... { } // error: uses ... but there's nothing to refine
  datatype Datatype ... // error: uses ... but there's nothing to refine
  codatatype Codatatype ... // error: uses ... but there's nothing to refine
  newtype Newtype ... // error: uses ... but there's nothing to refine
  class Class ... { } // error: uses ... but there's nothing to refine
  trait Trait ... { } // error: uses ... but there's nothing to refine
}

module StartingFromOpaqueType {
  abstract module A {
    type Ty<X> {
      const c: nat
      function F(x: nat): nat
      method M(x: nat) returns (r: nat)
    }
  }
  module OpaqueType refines A {
    type Ty<X, Y> ... { // error: wrong number of type parameters
      function F<Z>(x: nat): Z // error (x2): wrong number of type parametes, and wrong result type
      method M<Z>(x: nat) returns (r: Z) { r := c; } // error (x2): wrong number of type parameters, and wrong out-parameter type
    }
  }
  module Datatype refines A {
    datatype Ty = Make(x: int) { // error: wrong number of type parameters
      function F<Z>(x: nat): Z // error (x2): wrong number of type parametes, and wrong result type
      method M<Z>(x: nat) returns (r: Z) { r := c; } // error (x2): wrong number of type parametes, and wrong out-parameter type
    }
  }
  module Datatype' refines A {
    datatype Ty<X> = Make(c: int, F: int, M: int) // error (x3): members c,F,M already declared (reported on lines 31-33)
  }
  module Codatatype refines A {
    codatatype Ty = Make(w: int) { // error: wrong number of type parameters
      function F<Z>(x: nat): Z // error (x2): wrong number of type parametes, and wrong result type
      method M<Z>(x: nat) returns (r: Z) { r := c; } // error (x2): wrong number of type parametes, and wrong out-parameter type
    }
  }
  module Codatatype' refines A {
    codatatype Ty<X> = Make(c: int, F: int, M: int) // error (x3): members c,F,M already declared (reported on lines 31-33)
  }
  module Newtype refines A {
    newtype Ty = int { // error: wrong number of type parameters
      function F<Z>(x: nat): Z // error (x2): wrong number of type parametes, and wrong result type
      method M<Z>(x: nat) returns (r: Z) { r := c; } // error (x2): wrong number of type parametes, and wrong out-parameter type
    }
  }
  module Class refines A {
    class Ty { // error: wrong number of type parameters
      function F<Z>(x: nat): Z // error (x2): wrong number of type parametes, and wrong result type
      method M<Z>(x: nat) returns (r: Z) { r := c; } // error (x2): wrong number of type parametes, and wrong out-parameter type
    }
  }
  module Trait refines A {
    trait Ty { // error: wrong number of type parameters
      function F<Z>(x: nat): Z // error (x2): wrong number of type parametes, and wrong result type
      method M<Z>(x: nat) returns (r: Z) { r := c; } // error (x2): wrong number of type parametes, and wrong out-parameter type
    }
  }
  module TypeSynonym refines A {
    type Ty = int  // error: not allowed, since the original type has members
  }
}

module StartingFromDatatype {
  abstract module A {
    datatype Ty = Make(w: int) {
      const c: nat
      function F(x: nat): nat
      method M(x: nat) returns (r: nat)
    }
  }
  module OpaqueType refines A {
    type Ty ... // error: cannot refine a datatype with an opaque type
  }
  module OpaqueType' refines A {
    type Ty ... { } // error: cannot refine a datatype with an opaque type
  }
  module Datatype refines A {
    datatype Ty ... {
    }
  }
  module Codatatype refines A {
    codatatype Ty ... // error: cannot refine a datatype with a codatatype
  }
  module Newtype refines A {
    newtype Ty ... { } // error: cannot refine a datatype with a newtype
  }
  module Class refines A {
    class Ty ... { } // error: cannot refine a datatype with a class
  }
  module Trait refines A {
    trait Ty ... { } // error: cannot refine a datatype with a trait
  }
  module TypeSynonym refines A {
    type Ty = int  // error: cannot refine a datatype with a type synonym
  }
}

module StartingFromCodatatype {
  abstract module A {
    codatatype Ty = Make(w: int) {
      const c: nat
      function F(x: nat): nat
      method M(x: nat) returns (r: nat)
    }
  }
  module OpaqueType refines A {
    type Ty ... // error: cannot refine a codatatype with an opaque type
  }
  module Datatype refines A {
    datatype Ty ... // error: cannot refine a codatatype with a datatype
  }
  module Codatatype refines A {
    codatatype Ty ... {
    }
  }
  module Newtype refines A {
    newtype Ty ... { } // error: cannot refine a codatatype with a newtype
  }
  module Class refines A {
    class Ty ... { } // error: cannot refine a codatatype with a class
  }
  module Trait refines A {
    trait Ty ... { } // error: cannot refine a codatatype with a trait
  }
  module TypeSynonym refines A {
    type Ty = int  // error: cannot refine a codatatype with a type synonym
  }
}

module StartingFromNewtype {
  abstract module A {
    newtype Ty = int {
      const c: nat
      function F(x: nat): nat
      method M(x: nat) returns (r: nat)
    }
  }
  module OpaqueType refines A {
    type Ty ... // error: cannot refine a newtype with an opaque type
  }
  module Datatype refines A {
    datatype Ty ... // error: cannot refine a newtype with a datatype
  }
  module Codatatype refines A {
    codatatype Ty ... { // error: cannot refine a newtype with a codatatype
    }
  }
  module Class refines A {
    class Ty ... { } // error: cannot refine a newtype with a class
  }
  module Trait refines A {
    trait Ty ... { } // error: cannot refine a newtype with a trait
  }
  module TypeSynonym refines A {
    type Ty = int  // error: cannot refine a newtype with a type synonym
  }
}

module StartingFromClass {
  abstract module A {
    class Ty {
      const c: nat
      function F(x: nat): nat
      method M(x: nat) returns (r: nat)
    }
  }
  module OpaqueType refines A {
    type Ty ... // error: cannot refine a class with an opaque type
  }
  module Datatype refines A {
    datatype Ty ... // error: cannot refine a class with a datatype
  }
  module Codatatype refines A {
    codatatype Ty ... { // error: cannot refine a class with a codatatype
    }
  }
  module Newtype refines A {
    newtype Ty ... { } // error: cannot refine a class with a newtype
  }
  module Trait refines A {
    trait Ty ... { } // error: cannot refine a class with a trait
  }
  module TypeSynonym refines A {
    type Ty = int  // error: cannot refine a class with a type synonym
  }
}

module StartingFromTrait {
  abstract module A {
    trait Ty {
      const c: nat
      function F(x: nat): nat
      method M(x: nat) returns (r: nat)
    }
  }
  module OpaqueType refines A {
    type Ty ... // error: cannot refine a trait with an opaque type
  }
  module Datatype refines A {
    datatype Ty ... // error: cannot refine a trait with a datatype
  }
  module Codatatype refines A {
    codatatype Ty ... { // error: cannot refine a trait with a codatatype
    }
  }
  module Newtype refines A {
    newtype Ty ... { } // error: cannot refine a trait with a newtype
  }
  module Class refines A {
    class Ty ... { } // error: cannot refine a trait with a class
  }
  module TypeSynonym refines A {
    type Ty = int  // error: cannot refine a trait with a type synonym
  }
}
