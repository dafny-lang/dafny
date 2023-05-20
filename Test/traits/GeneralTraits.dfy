// RUN: %exits-with 2 %dafny /typeSystemRefresh:1 /generalTraits:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Tests {
  trait Parent { }

  datatype Dt extends Parent = Blue | Red

  type Abstract extends Parent

  method M(d: Dt, a: Abstract) {
    var p: Parent;
    p := d;
    p := a;
  }
}

module BadObjectExtensions {
  trait RefParent extends object { }
  datatype RefDt extends RefParent = Grey | Orange // error: datatype cannot extend object
  type RefAbstract extends RefParent // error: abstract type cannot extend object
}

module ExportThings {
  export ProvideThem
    provides Class, Trait
    provides TraitSub, AnotherClass
    provides ProvidedAbstractType
    reveals RevealedAbstractType

  trait {:termination false} Trait { }

  class Class extends Trait { }

  trait TraitSub extends Trait { }
  class AnotherClass extends TraitSub { }

  type ProvidedAbstractType extends Trait { } // fine
  type RevealedAbstractType extends Trait { } // error: the "extends" clause is exported, but Trait is not known to be a trait
}
