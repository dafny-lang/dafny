// RUN: %exits-with 2 %dafny /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module NamesThatDontExist {
  export
    // --- reveals
    reveals DoesNotExist  // error: unknown identiifer
    reveals Trait?.Valid  // error: not a type declaration with members
    reveals Klass?.Valid  // error: not a type declaration with members
    reveals Trait.Valid, Klass.Valid  // fine
    reveals Trait.NotThere  // error: not a member
    reveals TypeSynonym.Valid  // error: not a type declaration with members
    reveals Opaque.Valid  // error: not a member
    reveals DtValue.Valid  // error: not a type declaration with members
    reveals Color, Dt, Dt.Valid, Dt.M, Dt.N  // all good
    reveals Color.Magenta  // error: cannot mention datatype constructor in export
    reveals Color.More?  // error: cannot mention datatype discriminator in export
    reveals Color.u  // error: cannot mention datatype destructor in export
    reveals Trait?  // error: Trait and Trait? should be exported together, using Trait
    reveals Klass?  // error: Klass and Klass? should be exported together, using Klass
    // --- provides
    provides DoesNotExist  // error: unknown identiifer
    provides Trait?.Valid  // error: not a type declaration with members
    provides Klass?.Valid  // error: not a type declaration with members
    provides Trait.Valid, Klass.Valid  // fine
    provides Trait.NotThere  // error: not a member
    provides TypeSynonym.Valid  // error: not a type declaration with members
    provides Opaque.Valid  // error: not a member
    provides DtValue.Valid  // error: not a type declaration with members
    provides Color, Dt.Valid, Dt.M, Dt.N  // all good
    provides Color.Magenta  // error: cannot mention datatype constructor in export
    provides Color.More?  // error: cannot mention datatype discriminator in export
    provides Color.u  // error: cannot mention datatype destructor in export
    provides Trait?  // error: Trait and Trait? should be exported together, using Trait
    provides Klass?  // error: Klass and Klass? should be exported together, using Klass

  export DisallowDatatypeSignatureMembers0
    provides Dt
    provides Dt.X  // error: datatype constructors cannot be individually exported
    provides Dt.Cons?  // error: datatype discriminators cannot be individually exported
    provides Dt.u  // error: datatype denstructors cannot be individually exported

  export DisallowDatatypeSignatureMembers1
    reveals Dt
    provides Dt.X  // error: datatype constructors cannot be individually exported
    provides Dt.Cons?  // error: datatype discriminators cannot be individually exported
    provides Dt.u  // error: datatype denstructors cannot be individually exported

  trait Trait {
    ghost predicate Valid() { true }
    method M() { }
    var x: int
  }
  class Klass {
    constructor () { }
    constructor FromInt(w: int) { }
    ghost predicate Valid() { true }
    method M() { }
    var x: int
  }
  type TypeSynonym = Klass
  type Opaque
  datatype Color = Magenta | Cyan
  datatype Dt = X | Y | More(u: int) {
    ghost predicate Valid() { true }
    const M := 100
    static const N := 101
  }
  const DtValue: Dt := X

  export ExtremeVsPrefix0
    provides P, L
  export ExtremeVsPrefix1
    reveals P, L  // error: L is a lemma and cannot be revealed, only provided

  // The following two declarations also declare P# and L#, but the parser does not allow
  // such names in export declarations. (They are exported whenever P and L, respectively,
  // are.)
  least predicate P(r: real)
  least lemma L(r: real)

  method G()

  export ThingsThatCannotBeRevealed
    reveals G  // error: cannot be used with reveals
    provides Trait, Klass
    reveals Trait.M  // error: cannot be used with reveals
    reveals Trait.x  // error: cannot be used with reveals
    reveals Klass.M  // error: cannot be used with reveals
    reveals Klass.x  // error: cannot be used with reveals
    reveals Klass.FromInt  // error: cannot be used with reveals
  export ThoseThingsCanBeProvided
    provides G
    provides Trait, Klass
    provides Trait.M
    provides Trait.x
    provides Klass.M
    provides Klass.x
    provides Klass.FromInt
}

module ConsistencyErrors {
  // Providing a type exports the type name as an opaque type, along with any
  // type characteristics, type parameters, and the variance of the type parameters.
  // In the case of a class C, only type C can be provided, not C? (but both can be revealed).
  // Export a type does not automatically export datatype constructors, discriminators, or
  // destructors, class constructors, or type members are exported -- separate declarations
  // are needed for these (if allowed at all).
  export ProvideTypes
    provides Trait, Klass, Dt
  export P0 extends ProvideTypes  // error: export set not consistent (X, More?, u)
    provides DatatypeSignature
  export P1 extends ProvideTypes  // error: export set not consistent
    provides References
  export P2 extends ProvideTypes  // error: export set not consistent
    provides UsesValid
  export P3 extends ProvideTypes  // error: export set not consistent
    provides UsesStatic
  export P4 extends ProvideTypes  // error: export set not consistent
    provides UsesField

  export Constructor
    provides Klass.FromInt  // error: cannot provide constructor without revealing enclosing class
  export FieldsInProvidedType
    provides Trait, Klass
    provides Trait.x  // error: a mutable field can only be provided in a revealed type
    provides Klass.x  // error: a mutable field can only be provided in a revealed type
    provides Trait.M, Trait.N
    provides Klass.M, Klass.N
  export FieldsInRevealedType
    reveals Trait, Klass
    provides Trait.M, Trait.N, Trait.x
    provides Klass.M, Klass.N, Klass.x

  trait Trait {
    ghost predicate Valid() { true }
    const M := 100
    static const N := 101
    var x: int
  }
  class Klass {
    constructor () { }
    constructor FromInt(w: int) { }
    ghost predicate Valid() { true }
    const M := 100
    static const N := 101
    var x: int
  }
  datatype Dt = X | Y | More(u: int) {
    ghost predicate Valid() { true }
    const M := 100
    static const N := 101
  }

  method DatatypeSignature(t: Trait, k: Klass, d: Dt)
    requires d == X == Dt.X || (d.More? && d.u == 16)
  method References(t: Trait, k: Klass, d: Dt)
    requires (var o: object? := t; o) == (var o: object? := k; o)
  method UsesValid(t: Trait, k: Klass, d: Dt)
    requires t.Valid() && k.Valid() && d.Valid()
  method UsesStatic(t: Trait, k: Klass, d: Dt)
    requires Trait.N == Klass.N == Dt.N
  method UsesField(t: Trait, k: Klass, d: Dt)
    requires t.M == k.M == d.M

  export WhatIsKnownAboutProvidedClass0
    provides Trait
    provides Convert
  export WhatIsKnownAboutProvidedClass1
    provides Trait
    reveals Convert  // error: because Trait cannot be converted to object
  export WhatIsKnownAboutProvidedClass2
    provides Trait
    provides Convert?  // error: because Trait? is not a known type in this export set
  export WhatIsKnownAboutProvidedClass3
    provides Trait
    reveals Convert?  // error: because Trait? is not a known type in this export set
  export WhatIsKnownAboutRevealedClass0
    reveals Trait
    provides Convert, Convert?
  export WhatIsKnownAboutRevealedClass1
    reveals Trait
    reveals Convert, Convert?
  function Convert(x: Trait): object { x }
  function Convert?(x: Trait?): object? { x }
}

module GoodExports {
  export JustProvideTypes
    provides Trait, Klass, Dt
  export JustRevealTypes
    reveals Trait, Klass, Dt

  // Type members (except constructors in classes) can be explicitly exported,
  // as long as the type itself is either provided or revealed.
  export MembersOfProvidedTypes
    provides Trait, Klass, Dt
    provides Trait.Valid, Trait.M, Trait.N
    provides Klass.Valid, Klass.M, Klass.N
    provides Dt.Valid, Dt.M, Dt.N

  export MembersOfRevealedTypes
    reveals Trait, Klass, Dt
    provides Trait.Valid, Trait.M, Trait.N
    provides Klass.Valid, Klass.M, Klass.N
    provides Dt.Valid, Dt.M, Dt.N

  export BothConstructors
    reveals Klass
    provides Klass.FromInt

  trait Trait {
    ghost predicate Valid() { true }
    const M := 100
    static const N := 101
  }
  class Klass {
    constructor () { }
    constructor FromInt(w: int) { }
    ghost predicate Valid() { true }
    const M := 100
    static const N := 101
  }
  datatype Dt = X | Y | More(u: int) {
    ghost predicate Valid() { true }
    const M := 100
    static const N := 101
  }

  export ProvideExtreme
    provides P, L
    provides OpaqueFunction
  export RevealExtreme
    reveals P
    provides L
    reveals OpaqueFunction

  least predicate P(r: real)
  least lemma L(r: real)
  ghost function {:opaque} OpaqueFunction(r: real): int { 10 }
}

module Client_ProvideTypes {
  // This module checks that the outside world looks like it does inside module ConsistencyErrors above.
  import G = GoodExports`JustProvideTypes

  method DatatypeSignature(t: G.Trait, k: G.Klass, d: G.Dt)
    requires d == G.X || (d.More? && d.u == 16)  // error (3x): unknown identifiers X, More?, u
  method References(t: G.Trait, k: G.Klass, d: G.Dt)
    requires (var o: object? := t; o) == (var o: object? := k; o)
  method UsesValid(t: G.Trait, k: G.Klass, d: G.Dt)
    requires t.Valid() && k.Valid() && d.Valid()  // error (3x): unknown identifiers Valid
  method UsesStatic(t: G.Trait, k: G.Klass, d: G.Dt)
    requires G.Trait.N == G.Klass.N == G.Dt.N  // error (3x): unknown identifiers N
  method UsesField(t: G.Trait, k: G.Klass, d: G.Dt)
    requires t.M == k.M == d.M  // error (3x): unknown identifiers M
  method Constructor() {
    var k := new G.Klass();  // error: no anonymous constructor has been exported
  }
}

module Client_RevealTypes {
  // This module checks that the outside world looks like it does inside module ConsistencyErrors above.
  import G = GoodExports`JustRevealTypes

  method DatatypeSignature(t: G.Trait, tn: G.Trait?, k: G.Klass, kn: G.Klass?, d: G.Dt)
    requires d == G.X || (d.More? && d.u == 16)
  method Nullity(t: G.Trait, tn: G.Trait?, k: G.Klass, kn: G.Klass?, d: G.Dt)
    requires tn == null || kn == null
  method SubsetEquality(t: G.Trait, tn: G.Trait?, k: G.Klass, kn: G.Klass?, d: G.Dt)
    requires t == tn && k == kn
  method UsesValid(t: G.Trait, k: G.Klass, d: G.Dt)
    requires t.Valid() && k.Valid() && d.Valid()  // error (3x): unknown identifiers Valid
  method UsesStatic(t: G.Trait, k: G.Klass, d: G.Dt)
    requires G.Trait.N == G.Klass.N == G.Dt.N  // error (3x): unknown identifiers Valid
  method UsesField(t: G.Trait, k: G.Klass, d: G.Dt)
    requires t.M == k.M == d.M  // error (3x): unknown identifiers Valid
  method Constructor() {
    var k := new G.Klass();  // fine; the anonymous constructor gets exported with the class
  }
}

module Client_MembersOfProvidedTypes {
  // This module checks that the outside world looks like it does inside module ConsistencyErrors above.
  import G = GoodExports`MembersOfProvidedTypes

  method DatatypeSignature(t: G.Trait, k: G.Klass, d: G.Dt)
    requires d == G.X || (d.More? && d.u == 16)  // error (3x): unknown identifiers X, More?, u
  method References(t: G.Trait, k: G.Klass, d: G.Dt)
    requires (var o: object? := t; o) == (var o: object? := k; o)
  method UsesValid(t: G.Trait, k: G.Klass, d: G.Dt)
    requires t.Valid() && k.Valid() && d.Valid()
  method UsesStatic(t: G.Trait, k: G.Klass, d: G.Dt)
    requires G.Trait.N == G.Klass.N == G.Dt.N
  method UsesField(t: G.Trait, k: G.Klass, d: G.Dt)
    requires t.M == k.M == d.M
  method Constructor() {
    var k := new G.Klass();  // error: no anonymous constructor has been exported
  }
}

module Client_MembersOfRevealedTypes {
  // This module checks that the outside world looks like it does inside module ConsistencyErrors above.
  import G = GoodExports`MembersOfRevealedTypes

  method DatatypeSignature(t: G.Trait, tn: G.Trait?, k: G.Klass, kn: G.Klass?, d: G.Dt)
    requires d == G.X || (d.More? && d.u == 16)
  method Nullity(t: G.Trait, tn: G.Trait?, k: G.Klass, kn: G.Klass?, d: G.Dt)
    requires tn == null || kn == null
  method SubsetEquality(t: G.Trait, tn: G.Trait?, k: G.Klass, kn: G.Klass?, d: G.Dt)
    requires t == tn && k == kn
  method UsesValid(t: G.Trait, k: G.Klass, d: G.Dt)
    requires t.Valid() && k.Valid() && d.Valid()
  method UsesStatic(t: G.Trait, k: G.Klass, d: G.Dt)
    requires G.Trait.N == G.Klass.N == G.Dt.N
  method UsesField(t: G.Trait, k: G.Klass, d: G.Dt)
    requires t.M == k.M == d.M
  method Constructor() {
    var k := new G.Klass();  // fine; the anonymous constructor gets exported with the class
  }
}

module Client_BothConstructors {
  import G = GoodExports`BothConstructors

  method Constructors() returns (k: G.Klass) {
    k := new G.Klass();
    k := new G.Klass.FromInt(25);
  }
}

module Client_ProvideExtreme {
  import E = GoodExports`ProvideExtreme

  lemma Lemma(k: ORDINAL, r: real)
    requires E.P(r)
    requires E.P#[k](r)
  {
    E.L(r);
    E.L#[k](r);
    assert E.OpaqueFunction(r) == 10 by {
      reveal E.OpaqueFunction();  // error: no reveal lemma
    }
  }
}

module Client_RevealExtreme {
  import E = GoodExports`RevealExtreme

  lemma Lemma(k: ORDINAL, r: real)
    requires E.P(r)
    requires E.P#[k](r)
  {
    E.L(r);
    E.L#[k](r);
    assert E.OpaqueFunction(r) == 10 by {
      reveal E.OpaqueFunction();
    }
  }
}

module MultipleNamesForTheSameThing {
  module A {
    export
      provides T, T.F
    export Friends
      reveals T
      provides T.F
    newtype T = x | 0 <= x < 80 {
      ghost function F(): T { this }
      ghost predicate Q() { true }
    }
  }
  module B {
    import A
    type G = A.T
  }
  module C {
    export
      reveals X, Y
      provides Z, B
    export Friends extends C
      reveals Z
    import B
    type X = B.G
    type Y = B.A.T
    type Z = X
  }
  module D {
    export
      provides A
      reveals U
    import A
    type U = A.T
  }
  module PublicCaller {
    import A
    import B
    import C
    import D

    method M(o: A.T) returns (t: A.T, g: B.G, x: C.X, y: C.Y, z: C.Z, d: D.A.T, u: D.U) {
      t, g, x, y, d, u := o, o, o, o, o, o;
      t, g, x, y, d, u := g, g, g, g, g, g;
      t, g, x, y, d, u := x, x, x, x, x, x;
      t, g, x, y, d, u := y, y, y, y, y, y;
      t, g, x, y, d, u := d, d, d, d, d, d;
      t, g, x, y, d, u := u, u, u, u, u, u;

      z := x;  // error: nothing is known about C.Z
      z := o;  // error: nothing is known about C.Z
      t := 76;  // error: nothing is known about A.T
      assert u.F() == x;
      assert o.Q();  // error: Q has not been imported
    }
  }
  module FriendCaller {
    import A`Friends
    import B
    import C
    import D

    method M() returns (t: A.T, g: B.G, x: C.X, y: C.Y, z: C.Z, d: D.A.T, u: D.U) {
      var o: A.T := 76;
      t, g, x, y, d, u := o, o, o, o, o, o;
      t, g, x, y, d, u := g, g, g, g, g, g;
      t, g, x, y, d, u := x, x, x, x, x, x;
      t, g, x, y, d, u := y, y, y, y, y, y;
      t, g, x, y, d, u := d, d, d, d, d, d;
      t, g, x, y, d, u := u, u, u, u, u, u;

      z := x;  // error: nothing is known about C.Z
      z := o;  // error: nothing is known about C.Z
      t := 76;  // fine
      assert u.F() == x;
      assert o.Q();  // error: Q has not been imported
    }
  }
  module CloseFriendCaller {
    import A`Friends
    import B
    import C`Friends
    import D

    method M(o: A.T) returns (t: A.T, g: B.G, x: C.X, y: C.Y, z: C.Z, d: D.A.T, u: D.U) {
      t, g, x, y, d, u := o, o, o, o, o, o;
      t, g, x, y, d, u := g, g, g, g, g, g;
      t, g, x, y, d, u := x, x, x, x, x, x;
      t, g, x, y, d, u := y, y, y, y, y, y;
      t, g, x, y, d, u := d, d, d, d, d, d;
      t, g, x, y, d, u := u, u, u, u, u, u;

      z := x;
      z := o;
      t := 76;
      assert u.F() == x;
      assert o.Q();  // error: Q has not been imported
    }
  }
}

module StarLookupErrors {
  export RevealAll
    reveals *
  export RevealAllAndThenSome
    reveals *
    provides C.FromInt  // redundant in the face of "reveals *"
    provides B.F  // redundant in the face of "reveals *"
  export ProvideAll  // this excludes constructors and mutable fields
    provides *
  export ProvideAllAndThenSome
    provides *
    provides C.u  // error: cannot export mutable field without revealing class
    provides C.n
    provides C.FromInt  // error: cannot export constructor without revealing class
    provides C.PI
  export ProvideAllAndThenSomeMore
    provides *
    reveals C
    provides C.u
    provides C.FromInt

  datatype B = X | Y {
    function F(): int { if X? then 0 else 1 }
    function G(): int { 5 }
  }
  class C {
    var u: int
    const n: int
    static const PI := 3.14
    constructor () { }
    constructor FromInt(x: int) { }
    method M() { }
  }
}

module StarConsistencyErrors {
  export RevealAll
    reveals *
  export RevealAllAndThenSome
    reveals *
    provides C.FromInt  // redundant in the face of "reveals *"
    provides B.F  // redundant in the face of "reveals *"
  export ProvideAll  // this excludes constructors and mutable fields
    provides *
  export ProvideAllAndThenSome
    provides *
    provides C.PI
    reveals B.F  // error: functon body mentions X?, which isn't exported
    reveals B.G
  export ProvideAllAndThenSomeMore
    provides *
    reveals C
    provides C.u
    provides C.FromInt
    provides B.F  // just providing it is fine
    reveals B.G

  datatype B = X | Y {
    function F(): int { if X? then 0 else 1 }
    function G(): int { 5 }
  }
  class C {
    var u: int
    const n: int
    static const PI := 3.14
    constructor () { }
    constructor FromInt(x: int) { }
    method M() { }
  }
}

module StarsGood {
  export ProvideAll  // this excludes constructors and mutable fields
    provides *
  export ProvideAllAndThenSomeMore
    provides *
    reveals C
    provides C.u, C.FromInt, B.F, B.G
    reveals D
    reveals E

  datatype B = X | Y {
    function F(): int { if X? then 0 else 1 }
    function G(): int { 5 }
  }
  class C {
    var u: int
    const n: int
    static const PI := 3.14
    constructor () { }
    constructor FromInt(x: int) { }
    method M() { }
  }
  class D {
    var u: int
    static const PI := 3.14
    constructor FromInt(x: int) { }
    method M() { }
  }
  class E {
    var u: int
    static const PI := 3.14
    method M() { }
  }
  class F {
    var u: int
    static const PI := 3.14
    constructor FromInt(x: int) { }
    method M() { }
    static method Make() returns (f: F) {
      f := new F.FromInt(93);
    }
  }
}

module StarsGoodClient_All {
  import S = StarsGood`ProvideAll
  method M(b: S.B, c: S.C, d: S.D) {
    var f0 := b.F();
    var g0 := b.G();
    var u0 := c.u;  // error: u has not been exported
    var n0 := c.n;

    var r0 := S.C.PI;
    r0 := S.D.PI;
    r0 := S.E.PI;
    r0 := S.F.PI;

    var u1 := d.u;  // error: D.u is not exported

    var f: S.F;
    if * {
      f.M();  // error: to use d, it must first be initialized
      f := new S.F.FromInt(5);  // error (x2): FromInt has not been exported, and S.F.FromInt is not a class type
    } else {
      f := S.F.Make();
      f.M();
      var u1 := f.u;  // error: u has not been exported
    }
  }
}

module StarsGoodClient_AllAndMore {
  import S = StarsGood`ProvideAllAndThenSomeMore
  method M(b: S.B, c: S.C) {
    var f0 := b.F();
    var g0 := b.G();
    var u0 := c.u;
    var n0 := c.n;

    var r0 := S.C.PI;
    r0 := S.D.PI;
    r0 := S.E.PI;
    r0 := S.F.PI;

    var d: S.D;

    d := new S.D;  // error: no constructors of D are known, but that doesn't mean there aren't any
    var u1 := d.u;

    var e := new S.E;  // error: it is not known if E has any constructors or not, so this is not allowed

    var f: S.F;
    if * {
      f.M();  // error: to use d, it must first be initialized
      f := new S.F.FromInt(5);  // error: FromInt has not been exported, and it also isn't known that F is a class type
    } else {
      f := S.F.Make();
      f.M();
      var u1 := f.u;  // error: u has not been exported
    }
  }
}
