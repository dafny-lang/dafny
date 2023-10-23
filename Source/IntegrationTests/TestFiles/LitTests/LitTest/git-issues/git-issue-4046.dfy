// RUN: %exits-with 2 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Library {
  export
    provides WhoKnows
    provides TraitX, TraitY
    provides ClassX, ClassY, ClassZ

  type WhoKnows

  trait {:termination false} TraitX extends object { }
  trait {:termination false} TraitY { }

  class ClassX extends TraitX { }
  class ClassY extends TraitY { }
  class ClassZ { }
}

module Client1 {
  import Lib = Library

  class A extends Lib.WhoKnows { } // error: can only extend a trait
  class B extends Lib.TraitX { } // error: can only extend a trait
  class C extends Lib.TraitY { } // error: can only extend a trait
  class D extends Lib.ClassX { } // error: can only extend a trait
  class E extends Lib.ClassY { } // error: can only extend a trait
  class F extends Lib.ClassZ { } // error: can only extend a trait
  
  trait G extends Lib.TraitX { } // error: can only extend a trait
  trait H extends Lib.TraitY { } // error: can only extend a trait
}
