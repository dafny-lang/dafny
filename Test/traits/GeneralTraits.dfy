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

module ComparableTypes0 {
  trait TraitA { }
  trait TraitB extends TraitA { }
  trait TraitC extends TraitA { }
  newtype MyInt extends TraitB = x | 0 <= x < 100
  datatype Dt extends TraitB = Grey | Orange

  method Tests(o: object, a: TraitA, b: TraitB, c: TraitC, mi: MyInt, dt: Dt) {
    var r;
    r := mi == mi;

    r := o == mi; // error: object and MyInt are incomparable
    r := c == mi; // error: TraitC and MyInt are incomparable

    r := mi == o; // error: MyInt and object are incomparable
    r := mi == c; // error: MyInt and TraitC are incomparable

    r := dt == dt;

    r := o == dt; // error: object and Dt are incomparable
    r := c == dt; // error: TraitC and Dt are incomparable

    r := dt == o; // error: Dt and object are incomparable
    r := dt == c; // error: Dt and TraitC are incomparable
  }
}

module ComparableTypes1 {
  trait TraitA { }
  trait TraitB extends TraitA { }
  trait TraitC extends TraitA { }
  newtype MyInt extends TraitB = x | 0 <= x < 100
  datatype Dt extends TraitB = Grey | Orange

  method Tests(a: TraitA, b: TraitB, c: TraitC, mi: MyInt, dt: Dt) {
    var r;
    r := a == mi; // error: TraitA does not support equality
    r := b == mi; // error: TraitB does not support equality

    r := mi == a; // error: TraitA does not support equality
    r := mi == b; // error: TraitB does not support equality

    r := a == dt; // error: TraitA does not support equality
    r := b == dt; // error: TraitB does not support equality

    r := dt == a; // error: TraitA does not support equality
    r := dt == b; // error: TraitB does not support equality

    r := a == Grey; // error: TraitA does not support equality
    r := Grey == a; // error: TraitA does not support equality
  }
}
