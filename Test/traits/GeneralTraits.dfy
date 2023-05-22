// RUN: %exits-with 2 %dafny /typeSystemRefresh:1 /generalTraits:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Tests {
  trait Parent { }

  class Class extends Parent { }
  datatype Dt extends Parent = Blue | Red
  codatatype CoDt extends Parent = InfiniteBlue | InfiniteRed
  type Abstract extends Parent
  newtype MyInt extends Parent = int
  newtype MyConstrainedInt extends Parent = x | 0 <= x < 10

  method M(d: Dt, a: Abstract) {
    var p: Parent;
    p := d;
    p := a;
  }
}

module BadObjectExtensions {
  trait Parent extends object { }
  class Class extends Parent { }
  datatype RefDt extends Parent = Grey | Orange // error: datatype cannot extend object
  codatatype CoDt extends Parent = InfiniteBlue | InfiniteRed // error: datatype cannot extend object
  type RefAbstract extends Parent // error: abstract type cannot extend object
  newtype MyInt extends Parent = int // error: abstract type cannot extend object
  newtype MyConstrainedInt extends Parent = x | 0 <= x < 10 // error: abstract type cannot extend object
}

module ExportThings {
  export Revealthem
    reveals Trait, Class, Dt, CoDt, Abstract, MyInt, MyConstrainedInt
    reveals TraitSub, AnotherClass
    reveals ProvidedAbstractType
    reveals RevealedAbstractType
  export ProvideThem // error: inconsistent export set
    provides Trait, Class, Dt, CoDt, Abstract, MyInt, MyConstrainedInt
    provides  TraitSub, AnotherClass
    provides ProvidedAbstractType
    reveals RevealedAbstractType

  trait Trait { }

  class Class extends Trait { }
  datatype Dt extends Trait = Grey | Orange
  codatatype CoDt extends Trait = InfiniteBlue | InfiniteRed
  type Abstract extends Trait
  newtype MyInt extends Trait = int
  newtype MyConstrainedInt extends Trait = x | 0 <= x < 10

  trait TraitSub extends Trait { }
  class AnotherClass extends TraitSub { }

  type ProvidedAbstractType extends Trait { } // fine
  type RevealedAbstractType extends Trait { } // error: the "extends" clause is exported, but Trait is not known to be a trait
}
