// RUN: %exits-with 2 %build --general-traits legacy "%s" > "%t"
// RUN: %exits-with 2 %build --general-traits datatype "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module Tests {
  module M {
    trait {:termination false} MX { }
    trait {:termination false} MY extends object { }
    trait {:termination false} MZ extends MX, MY { }
  }

  trait Z extends Q { }
  trait Q { }
  trait A extends Z, object { }
  trait B extends A { }
  trait C extends A { }
  trait D extends B, C { }

  trait E extends M.MX { }
  trait F extends M.MY { }
  trait G extends M.MZ { }

  class MyClassA extends C, object, D { }
  class MyClassB extends C, D { }
  class MyClassC { }

  method Tests() {
    var mx: M.MX?; // error: no type MX?
    var my: M.MY?;
    var mz: M.MZ?;

    var z: Z?; // error: no type Z?
    var q: Q?; // error: no type Q?
    var a: A?;
    var b: B?;
    var c: C?;
    var d: D?;

    var e: E?; // error: no type E?
    var f: F?;
    var g: G?;

    var ca: MyClassA?;
    var cb: MyClassB?;
    var cc: MyClassC?;
  }
}

module MutableFields {
  datatype Dt<A> = Blue | Bucket(diameter: real) | Business(trendy: bool, a: A)
  {
    var x: int  // error: mutable fields not allowed in datatypes
  }
  newtype MyInt = int
  {
    var x: int  // error: mutable fields not allowed in newtypes
  }
  newtype Pos = x | 0 < x witness 1
  {
    var x: int  // error: mutable fields not allowed in newtypes
  }
  type Abstract {
    var x: int  // error: mutable fields not allowed in abstract types
  }
  class Class {
    var x: int
  }
  trait NonReferenceTrait {
    var x: int  // error: mutable fields not allowed in non-reference trait types
  }
  trait ReferenceTrait extends object {
    var x: int
  }
  trait AnotherReferenceTrait extends ReferenceTrait {
    var y: int
  }
}

module Exports {
  module BadLibrary {
    export // error: inconsistent export set
      reveals Class, TraitSub
      provides Trait

    trait Trait { }

    // The following is allowed if Trait is known to be a trait.
    // However, in the export set, Trait is known only as an abstract type.
    class Class extends Trait { } // error (in export set): a type can only extend traits

    // Ditto.
    trait TraitSub extends Trait { } // error (in export set): a type can only extend traits
  }

  module GoodLibrary {
    export RevealThem
      reveals Class, TraitSub, Trait
    export ProvideThem
      provides Class, TraitSub, Trait, AnotherClass

    trait {:termination false} Trait { }

    class Class extends Trait { }

    trait TraitSub extends Trait { }
    class AnotherClass extends TraitSub { }
  }

  module Client0 {
    import G = GoodLibrary`RevealThem

    class MyClass extends G.Trait { }
    trait MyTrait extends G.Trait { }
  }

  module Client1 {
    import G = GoodLibrary`ProvideThem

    class MyClass extends G.Trait { } // error: G.Trait is not known to be a trait
    trait MyTrait extends G.Trait { } // error: G.Trait is not known to be a trait
  }
}

module HintInErrorMessage {
  trait Trait { }

  method M(t: Trait?) { // error: no such thing as 'Trait?' (nice error-message hint, huh?)
  }
}

module NameClash {
  trait AA { } // error (but only for implicit "extends object"): name clash

  type AA?
}

module UninitializedConsts {
  type AutoInit = x | 12 <= x < 17 witness 16
  type Nonempty = x | 12 <= x < 17 ghost witness 16
  type PossiblyEmpty = x | 12 <= x < 17 witness *

  datatype Dt<A> = Blue | Bucket(diameter: real) | Business(trendy: bool, aa: A)
  {
    const a: AutoInit
    const b: AutoInit := 15
    ghost const A: AutoInit
    ghost const B: AutoInit := 15

    const g: Nonempty // error: requires initialization
    const h: Nonempty := 15
    ghost const G: Nonempty
    ghost const H: Nonempty := 15

    const s: PossiblyEmpty // error: requires initialization
    const t: PossiblyEmpty := 15
    ghost const S: PossiblyEmpty // error: requires initialization
    ghost const T: PossiblyEmpty := 15
  }

  newtype MyInt = int
  {
    const a: AutoInit
    const b: AutoInit := 15
    ghost const A: AutoInit
    ghost const B: AutoInit := 15

    const g: Nonempty // error: requires initialization
    const h: Nonempty := 15
    ghost const G: Nonempty
    ghost const H: Nonempty := 15

    const s: PossiblyEmpty // error: requires initialization
    const t: PossiblyEmpty := 15
    ghost const S: PossiblyEmpty // error: requires initialization
    ghost const T: PossiblyEmpty := 15
  }

  newtype Pos = x | 0 < x witness 1
  {
    const a: AutoInit
    const b: AutoInit := 15
    ghost const A: AutoInit
    ghost const B: AutoInit := 15

    const g: Nonempty // error: requires initialization
    const h: Nonempty := 15
    ghost const G: Nonempty
    ghost const H: Nonempty := 15

    const s: PossiblyEmpty // error: requires initialization
    const t: PossiblyEmpty := 15
    ghost const S: PossiblyEmpty // error: requires initialization
    ghost const T: PossiblyEmpty := 15
  }

  type Abstract {
    const a: AutoInit
    const b: AutoInit := 15
    ghost const A: AutoInit
    ghost const B: AutoInit := 15

    const g: Nonempty // error: requires initialization
    const h: Nonempty := 15
    ghost const G: Nonempty
    ghost const H: Nonempty := 15

    const s: PossiblyEmpty // error: requires initialization
    const t: PossiblyEmpty := 15
    ghost const S: PossiblyEmpty // error: requires initialization
    ghost const T: PossiblyEmpty := 15
  }

  trait NonReferenceTrait {
    const a: AutoInit
    const b: AutoInit := 15
    ghost const A: AutoInit
    ghost const B: AutoInit := 15

    const g: Nonempty // error: requires initialization
    const h: Nonempty := 15
    ghost const G: Nonempty
    ghost const H: Nonempty := 15

    const s: PossiblyEmpty // error: requires initialization
    const t: PossiblyEmpty := 15
    ghost const S: PossiblyEmpty // error: requires initialization
    ghost const T: PossiblyEmpty := 15
  }

  trait ReferenceTrait extends object {
    // the implementing class will provide initialization as needed
    const a: AutoInit
    const b: AutoInit := 15
    ghost const A: AutoInit
    ghost const B: AutoInit := 15

    const g: Nonempty
    const h: Nonempty := 15
    ghost const G: Nonempty
    ghost const H: Nonempty := 15

    const s: PossiblyEmpty
    const t: PossiblyEmpty := 15
    ghost const S: PossiblyEmpty
    ghost const T: PossiblyEmpty := 15
  }

  class Class {
    const a: AutoInit
    const b: AutoInit := 15
    ghost const A: AutoInit
    ghost const B: AutoInit := 15

    const g: Nonempty
    const h: Nonempty := 15
    ghost const G: Nonempty
    ghost const H: Nonempty := 15

    const s: PossiblyEmpty
    const t: PossiblyEmpty := 15
    ghost const S: PossiblyEmpty
    ghost const T: PossiblyEmpty := 15

    constructor () {
      g := 12;
      s := 12;
      S := 12;
    }
  }

  class ClassWithParent extends ReferenceTrait {
    constructor () {
      g := 12;
      s := 12;
      S := 12;
    }
  }

  class ClassWithParentWithoutConstructor extends ReferenceTrait { // error: class must provide a constructor
  }
}

module UninitializedStaticConsts {
  type AutoInit = x | 12 <= x < 17 witness 16
  type Nonempty = x | 12 <= x < 17 ghost witness 16
  type PossiblyEmpty = x | 12 <= x < 17 witness *

  datatype Dt<A> = Blue | Bucket(diameter: real) | Business(trendy: bool, aa: A)
  {
    static const a: AutoInit
    static const b: AutoInit := 15
    static ghost const A: AutoInit
    static ghost const B: AutoInit := 15

    static const g: Nonempty // error: requires initialization
    static const h: Nonempty := 15
    static ghost const G: Nonempty
    static ghost const H: Nonempty := 15

    static const s: PossiblyEmpty // error: requires initialization
    static const t: PossiblyEmpty := 15
    static ghost const S: PossiblyEmpty // error: requires initialization
    static ghost const T: PossiblyEmpty := 15
  }

  newtype MyInt = int
  {
    static const a: AutoInit
    static const b: AutoInit := 15
    static ghost const A: AutoInit
    static ghost const B: AutoInit := 15

    static const g: Nonempty // error: requires initialization
    static const h: Nonempty := 15
    static ghost const G: Nonempty
    static ghost const H: Nonempty := 15

    static const s: PossiblyEmpty // error: requires initialization
    static const t: PossiblyEmpty := 15
    static ghost const S: PossiblyEmpty // error: requires initialization
    static ghost const T: PossiblyEmpty := 15
  }

  newtype Pos = x | 0 < x witness 1
  {
    static const a: AutoInit
    static const b: AutoInit := 15
    static ghost const A: AutoInit
    static ghost const B: AutoInit := 15

    static const g: Nonempty // error: requires initialization
    static const h: Nonempty := 15
    static ghost const G: Nonempty
    static ghost const H: Nonempty := 15

    static const s: PossiblyEmpty // error: requires initialization
    static const t: PossiblyEmpty := 15
    static ghost const S: PossiblyEmpty // error: requires initialization
    static ghost const T: PossiblyEmpty := 15
  }

  type Abstract {
    static const a: AutoInit
    static const b: AutoInit := 15
    static ghost const A: AutoInit
    static ghost const B: AutoInit := 15

    static const g: Nonempty // error: requires initialization
    static const h: Nonempty := 15
    static ghost const G: Nonempty
    static ghost const H: Nonempty := 15

    static const s: PossiblyEmpty // error: requires initialization
    static const t: PossiblyEmpty := 15
    static ghost const S: PossiblyEmpty // error: requires initialization
    static ghost const T: PossiblyEmpty := 15
  }

  trait NonReferenceTrait {
    static const a: AutoInit
    static const b: AutoInit := 15
    static ghost const A: AutoInit
    static ghost const B: AutoInit := 15

    static const g: Nonempty // error: requires initialization
    static const h: Nonempty := 15
    static ghost const G: Nonempty
    static ghost const H: Nonempty := 15

    static const s: PossiblyEmpty // error: requires initialization
    static const t: PossiblyEmpty := 15
    static ghost const S: PossiblyEmpty // error: requires initialization
    static ghost const T: PossiblyEmpty := 15
  }

  trait ReferenceTrait extends object {
    static const a: AutoInit
    static const b: AutoInit := 15
    static ghost const A: AutoInit
    static ghost const B: AutoInit := 15

    static const g: Nonempty // error: requires initialization
    static const h: Nonempty := 15
    static ghost const G: Nonempty
    static ghost const H: Nonempty := 15

    static const s: PossiblyEmpty // error: requires initialization
    static const t: PossiblyEmpty := 15
    static ghost const S: PossiblyEmpty // error: requires initialization
    static ghost const T: PossiblyEmpty := 15
  }

  class Class {
    static const a: AutoInit
    static const b: AutoInit := 15
    static ghost const A: AutoInit
    static ghost const B: AutoInit := 15

    static const g: Nonempty // error: requires initialization
    static const h: Nonempty := 15
    static ghost const G: Nonempty
    static ghost const H: Nonempty := 15

    static const s: PossiblyEmpty // error: requires initialization
    static const t: PossiblyEmpty := 15
    static ghost const S: PossiblyEmpty // error: requires initialization
    static ghost const T: PossiblyEmpty := 15

    constructor () {
    }
  }

  class ClassWithParent extends ReferenceTrait {
    constructor () {
    }
  }

  class ClassWithParentWithoutConstructor extends ReferenceTrait {
  }
}

module ComparableTypes0 {
  trait ObjectA extends object { }
  trait ObjectB extends ObjectA { }
  trait ObjectC extends object { }

  method ReferenceEquality(o: object, a: ObjectA, b: ObjectB, c: ObjectC) {
    var r;
    r := o == o && o == a && o == b && o == c;
    r := o in {o, a, b, c} && o in {a, b};

    r := a == o && a == a && a == b;
    r := a == c; // error: ObjectA and ObjectC are not comparable types
    r := a in {o, a, b, c} && a in {a, b};

    r := b == o && b == a && b == b;
    r := b == c; // error: ObjectB and ObjectC are not comparable types
    r := b in {o, a, b, c} && b in {a, b};
  }

  trait TraitA { }
  trait TraitB extends TraitA { }

  method NonReferenceEquality(o: object, a: TraitA, b: TraitB) {
    var r;
    r := o == o;
    r := o == a; // error: object and TraitA are incomparable
    r := o == b; // error: object and TraitB are incomparable
    r := a == o; // error: TraitA and object are incomparable
    r := b == o; // error: TraitB and object are incomparable
  }
}

module ComparableTypes1 {
  trait TraitA { }
  trait TraitB extends TraitA { }

  method NonReferenceEquality(a: TraitA, b: TraitB) {
    var r;
    r := a == b; // error: TraitA and TraitB don't necessarily support equality
  }
}

module EqualitySupport {
  trait TraitA { }
  trait TraitB extends TraitA { }

  method NonReferenceEquality(a: TraitA, b: TraitB) {
    var r;
    r := a == a; // error: TraitA is not an equality-supporting type
    r := b == b; // error: TraitB is not an equality-supporting type
    r := a in {a}; // error: TraitA is not an equality-supporting type
  }
}
