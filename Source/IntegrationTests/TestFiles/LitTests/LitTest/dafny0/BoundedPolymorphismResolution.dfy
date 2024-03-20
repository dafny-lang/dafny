// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s" -- --general-traits=datatype

module BadTypeNames {
  datatype DT<W extends Unknown> = Dt(w: W) // error: what is Unknown?

  type Syn<X extends Unknown> = DT<X> // error: what is Unknown?

  class Class<Y extends Unknown> { // error: what is Unknown?
  }

  trait AnotherTrait<Z extends Unknown> { // error: what is Unknown?
  }

  type Abstract<V extends Unknown> // error: what is Unknown?

  trait Generic<Q> { }

  codatatype Mutual<A extends Generic<Z>, B extends Generic<A>> = More(Mutual) // error: what is Z?

  function Function<K extends Unknown>(k: K): int { 2 } // error: what is Unknown?

  method Method<L extends Unknown>(l: L) { } // error: what is Unknown?

  least predicate Least<M extends Unknown>(m: M) { true } // error: what is Unknown?

  greatest lemma Greatest<N extends Unknown>(n: N) { } // error: what is Unknown?

  iterator Iter<O extends Unknown>(o: O) { } // error: what is Unknown?
}

module AsIsResolve0 {
  trait Trait extends object {
    const n: int
  }
  trait AnotherTrait { }

  method M<X extends Trait>(x: X) returns (b: bool, t: Trait, u: int) {
    t := x; // error: need to cast to Trait first
    b := x is Trait; // (legacy error)
    b := x is AnotherTrait; // error: AnotherTrait is not compatible with X
    b := x is object; // (legacy error)
    t := x as Trait; // (legacy error)
    u := t.n;
    assert x == t; // (legacy error)
  }
}

module AsIsResolve1 {
  trait Trait {
    const n: int
  }

  method Q<Y(==) extends Trait>(y: Y) returns (t: Trait, u: int) {
    t := y as Trait; // (legacy error)
    u := (y as Trait).n; // (legacy error)
    u := y.n; // error: y needs to be cast to Trait before .n can be accessed
  }

  method Nullable<Z extends object>(z: Z) returns (b: bool) {
    var n;
    n := z;
    b := (z as object) as object? == null; // (legacy error)
    n := null; // error: although n is a reference type, there is no type Z?
  }

  method T<Z extends object?>(z: Z) {
    var n;
    n := z;
    n := null; // error: although n extends object?, Z may have constraints that exclude "null"
  }

  trait XTrait<X> { }

  method U<T extends XTrait<int>>(t: T) {
    var a := t as XTrait<int>; // (legacy error)
    var b := t as XTrait<bool>; // error: non-compatible types
  }
}
  
module AsIsResolve2 {
  trait Trait {
    const n: int
  }

  method A<X(==) extends Trait>(x: X, t: Trait) returns (b: bool) {
    b := x is X;
    b := x is Trait; // (legacy error)
    b := t is X; // error: not allowed in compiled code
    b := t is Trait;
  }

  method B<X(==) extends Trait>(x: X, t: Trait) returns (ghost g: bool, b: bool) {
    b := x is X;
    b := x is Trait; // (legacy error)
    g := t is X; // (legacy error)
    b := t is Trait;
  }

  method N<X extends Trait>(x: X) returns (b: bool, t: Trait) {
    t := x as Trait; // (legacy error)
    assert x == t; // (legacy error)
    ghost var gb := t is X; // (legacy error)
    b := t is X; // error: this is not allowed in compiled code
  }
}

module AsIsResolve3 {
  trait Trait {
    const n: int
  }

  method P<Y extends Trait>(y: Y) returns (b: bool, t: Trait) {
    t := y as Trait; // (legacy error)
    assert y == t; // (legacy error)
    b := y == t; // error: we don't know if y supports equality
  }

  method R<Y(==) extends Trait>(y: Y) returns (b: bool, t: Trait) {
    t := y as Trait; // (legacy error)
    b := y == t; // error: Trait not known to support equality
  }

  method S<Y extends object>(y: Y) returns (b: bool, obj: object) {
    obj := y as object; // (legacy error)
    b := y == obj; // error: Y not known to support equality
  }

  method Finally<Y(==) extends object>(y: Y) returns (b: bool, obj: object) {
    obj := y as object; // (legacy error)
    b := y == obj; // both Y and object support equality, so we're good // (legacy error)
  }
}

module AsIsResolve4 {
  trait Trait { }
  class Class extends Trait { }
  
  method M<X extends Trait>(x: X) {
    var a0 := x as X; // (legacy error)
    var a1 := x as Trait; // (legacy error)
    var a2 := x as Class; // error
    var a3 := x as int; // error
  }
}
