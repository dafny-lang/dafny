// RUN: %dafny /dprint:"%t.dprint" "%s" > "%t"
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
    reveals Opaque.Valid  // error: not a type declaration with members
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
    provides Opaque.Valid  // error: not a type declaration with members
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

  class Trait {
    predicate Valid() { true }
  }
  class Klass {
    constructor () { }
    constructor FromInt(w: int) { }
    predicate Valid() { true }
  }
  type TypeSynonym = Klass
  type Opaque
  datatype Color = Magenta | Cyan
  datatype Dt = X | Y | More(u: int) {
    predicate Valid() { true }
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
  inductive predicate P(r: real)
  inductive lemma L(r: real)
}

module ConsistencyErrors {
  // Providing a type exports the type name as an opaque type, along with any
  // type characteristics, type parameters, and the variance of the type parameters.
  // In the case of a class C, both type C and C? are exported.
  // But no datatype constructors, discriminators, or destructors, class constructors,
  // or type members are exported.
  export ProvideTypes
    provides Trait, Klass, Dt
  export P0 extends ProvideTypes  // error: export set not consistent (X, More?, u)
    provides DatatypeSignature  // TODO: should be error
  export P1 extends ProvideTypes
    provides Nullity  // TODO: should be error
  export P2 extends ProvideTypes  // error: export set not consistent
    provides SubsetEquality
  export P3 extends ProvideTypes  // error: export set not consistent
    provides UsesValid
  export P4 extends ProvideTypes  // error: export set not consistent
    provides UsesStatic
  export P5 extends ProvideTypes  // error: export set not consistent
    provides UsesField

  export Constructor
    provides Klass.FromInt  // error: cannot provide constructor without revealing enclosing class

  class Trait {
    predicate Valid() { true }
    const M := 100
    static const N := 101
  }
  class Klass {
    constructor () { }
    constructor FromInt(w: int) { }
    predicate Valid() { true }
    const M := 100
    static const N := 101
  }
  datatype Dt = X | Y | More(u: int) {
    predicate Valid() { true }
    const M := 100
    static const N := 101
  }

  method DatatypeSignature(t: Trait, tn: Trait?, k: Klass, kn: Klass?, d: Dt)
    requires d == X == Dt.X || (d.More? && d.u == 16)
  method Nullity(t: Trait, tn: Trait?, k: Klass, kn: Klass?, d: Dt)
    requires tn == null || kn == null
  method SubsetEquality(t: Trait, tn: Trait?, k: Klass, kn: Klass?, d: Dt)
    requires t == tn && k == kn
  method UsesValid(t: Trait, k: Klass, d: Dt)
    requires t.Valid() && k.Valid() && d.Valid()
  method UsesStatic(t: Trait, k: Klass, d: Dt)
    requires Trait.N == Klass.N == Dt.N
  method UsesField(t: Trait, k: Klass, d: Dt)
    requires t.M == k.M == d.M
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

  class Trait {
    predicate Valid() { true }
    const M := 100
    static const N := 101
  }
  class Klass {
    constructor () { }
    constructor FromInt(w: int) { }
    predicate Valid() { true }
    const M := 100
    static const N := 101
  }
  datatype Dt = X | Y | More(u: int) {
    predicate Valid() { true }
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

  inductive predicate P(r: real)
  inductive lemma L(r: real)
  function {:opaque} OpaqueFunction(r: real): int { 10 }
}

module Client_ProvideTypes {
  // This module checks that the outside world looks like it does inside module ConsistencyErrors above.
  import G = GoodExports`JustProvideTypes

  method DatatypeSignature(t: G.Trait, tn: G.Trait?, k: G.Klass, kn: G.Klass?, d: G.Dt)
    requires d == G.X || (d.More? && d.u == 16)  // error (3x): unknown identifiers X, More?, u
  method Nullity(t: G.Trait, tn: G.Trait?, k: G.Klass, kn: G.Klass?, d: G.Dt)
    requires tn == null || kn == null  // TODO: should be error
  method SubsetEquality(t: G.Trait, tn: G.Trait?, k: G.Klass, kn: G.Klass?, d: G.Dt)
    requires t == tn && k == kn  // TODO: should be error
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
    requires t.Valid() && k.Valid() && d.Valid()  // error (TODO 3x): unknown identifiers Valid
  method UsesStatic(t: G.Trait, k: G.Klass, d: G.Dt)
    requires G.Trait.N == G.Klass.N == G.Dt.N  // error (TODO 3x): unknown identifiers Valid
  method UsesField(t: G.Trait, k: G.Klass, d: G.Dt)
    requires t.M == k.M == d.M  // error (TODO 3x): unknown identifiers Valid
  method Constructor() {
    var k := new G.Klass();  // fine; the anonymous constructor gets exported with the class
  }
}

module Client_MembersOfProvidedTypes {
  // This module checks that the outside world looks like it does inside module ConsistencyErrors above.
  import G = GoodExports`MembersOfProvidedTypes

  method DatatypeSignature(t: G.Trait, tn: G.Trait?, k: G.Klass, kn: G.Klass?, d: G.Dt)
    requires d == G.X || (d.More? && d.u == 16)  // error (3x): unknown identifiers X, More?, u
  method Nullity(t: G.Trait, tn: G.Trait?, k: G.Klass, kn: G.Klass?, d: G.Dt)
    requires tn == null || kn == null  // TODO: should be error
  method SubsetEquality(t: G.Trait, tn: G.Trait?, k: G.Klass, kn: G.Klass?, d: G.Dt)
    requires t == tn && k == kn  // TODO: should be error
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
