// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Types {
  trait A<X> { }
  trait B<X> { }
  trait C<Y> extends A<seq<Y>> { }
  trait D<Z> extends B<int>, C<Z> { }
  class K<X> { }
  class L<Y> extends A<Y> { }
  class M<W> extends D<(W, W)> { }
  type Opaque
  type RefSyn = L<int>
  type RefSyn? = L?<int>
  type ValSyn = ORDINAL
  type RefSubset = d: D<int> | true
}

module NoReferenceTypes {
  import opened Types

  method Assignment<V>(m: M, m0: M?) {
    var i: int := m; // error: M not assignable to int
    var o: Opaque := m; // error: M not assignable to Opaque
    var vs: ValSyn := m; // error: M not assignable to ValSyn
    i := m0; // error: M? not assignable to int
    o := m0; // error: M? not assignable to Opaque
    vs := m0; // error: M? not assignable to ValSyn
  }

  method As(m: M, m0: M?) {
    var i := m as int; // error: type conversion to int not possible from M
    var o := m as Opaque; // error: type conversion to Opaque not possible from M
    var vs := m as ValSyn; // error: type conversion to ValSyn not possible from M
    i := m0 as int; // error: type conversion to int not possible from M?
    o := m0 as Opaque; // error: type conversion to Opaque not possible from M?
    vs := m0 as ValSyn; // error: type conversion to ValSyn not possible from M?
  }
}

module Assignments {
  import opened Types

  method AssignmentToSupertype<V>(m: M, m0: M?) {
    var a: A := m;
    var b: B := m;
    var c: C := m;
    var d: D := m;
    var k: K := m; // error: M not assignable to K
    var l: L := m; // error: M not assignable to L
    var m': M := m;
    var rs: RefSyn := m; // error: M not assignable to RefSyn

    a := m0;
    b := m0;
    c := m0;
    d := m0;
    k := m0; // error: M? not assignable to K
    l := m0; // error: M? not assignable to L
    m' := m0;
    rs := m0; // error: M? not assignable to RefSyn

    var a0: A? := m;
    var b0: B? := m;
    var c0: C? := m;
    var d0: D? := m;
    var k0: K? := m; // error: M not assignable to K?
    var l0: L? := m; // error: M not assignable to L?
    var m0': M? := m;
    var rs0: RefSyn? := m; // error: M not assignable to RefSyn?

    a0 := m0;
    b0 := m0;
    c0 := m0;
    d0 := m0;
    k0 := m0; // error: M? not assignable to K?
    l0 := m0; // error: M? not assignable to L?
    m0' := m0;
    rs0 := m0; // error: M? not assignable to RefSyn?
  }
}

module As {
  import opened Types

  method AsToSupertype<V>(m: M, m0: M?) {
    var a := m as A;
    var b := m as B;
    var c := m as C;
    var d := m as D;
    var k := m as K; // error: M not assignable to K
    var l := m as L; // error: M not assignable to L
    var m' := m as M;
    var rs := m as RefSyn; // error: M not assignable to RefSyn

    a := m0 as A;
    b := m0 as B;
    c := m0 as C;
    d := m0 as D;
    k := m0 as K; // error: M? not assignable to K
    l := m0 as L; // error: M? not assignable to L
    m' := m0 as M;
    rs := m0 as RefSyn; // error: M? not assignable to RefSyn

    var a0 := m as A?;
    var b0 := m as B?;
    var c0 := m as C?;
    var d0 := m as D?;
    var k0 := m as K?; // error: M not assignable to K?
    var l0 := m as L?; // error: M not assignable to L?
    var m0' := m as M?;

    a0 := m0 as A?;
    b0 := m0 as B?;
    c0 := m0 as C?;
    d0 := m0 as D?;
    k0 := m0 as K?; // error: M? not assignable to K?
    l0 := m0 as L?; // error: M? not assignable to L?
    m0' := m0 as M?;
  }

  method AsToSubtype<V>(o: object, a: A<seq<(V, V)>>, b: B<int>, c: C<(V, V)>, d: D<(V, V)>, k: K, l: L, rs: RefSyn) returns (m: M, m0: M?) {
    m := o as M;
    m := a as M;
    m := b as M;
    m := c as M;
    m := d as M;
    m := k as M; // error: K is not assignable to M
    m := l as M; // error: L is not assignable to M
    m := rs as M; // error: RefSyn is not assignable to M

    m0 := o as M?;
    m0 := a as M?;
    m0 := b as M?;
    m0 := c as M?;
    m0 := d as M?;
    m0 := k as M?; // error: K is not assignable to M?
    m0 := l as M?; // error: L is not assignable to M?
    m0 := rs as M?; // error: RefSyn is not assignable to M?
  }

  method AsToSubtype?<V>(o0: object?, a0: A?<seq<(V, V)>>, b0: B?<int>, c0: C?<(V, V)>, d0: D?<(V, V)>, k0: K?, l0: L?, rs0: RefSyn?) returns (m: M, m0: M?) {
    m := o0 as M;
    m := a0 as M;
    m := b0 as M;
    m := c0 as M;
    m := d0 as M;
    m := k0 as M; // error: K? is not assignable to M
    m := l0 as M; // error: L? is not assignable to M
    m := rs0 as M; // error: RefSyn? is not assignable to M

    m0 := o0 as M?;
    m0 := a0 as M?;
    m0 := b0 as M?;
    m0 := c0 as M?;
    m0 := d0 as M?;
    m0 := k0 as M?; // error: K? is not assignable to M?
    m0 := l0 as M?; // error: L? is not assignable to M?
    m0 := rs0 as M?; // error: RefSyn? is not assignable to M?
  }
}

module IsTests {
  import opened Types

  newtype Odd = x | x % 2 == 1
  type True = b: bool | b
  datatype List<T> = Nil | Cons(T, List<T>)
  type VeryShortList<T> = xs: List<T> | xs == Nil
  codatatype Stream<T> = More(T, Stream<T>)

  method Test(m: M<string>) returns (b: bool) {
    b := 3 is int;
    b := 3 is bv7;
    b := 3 is ORDINAL;
    b := 3 is nat;
    b := 3 is Odd;
    b := 3 as char is char;
    b := 'A' is char;
    b := false is True;

    b := m is object;
    b := m is A<bv10>; // error: M<string> not assignable to A<bv10>
    b := m is C<(string, string)>;
    b := m as C<(int, real)> is C<(int, real)>; // error: "as" is not allowed, but "is" is
    b := null is C<(int, real)>;
    var n: object? := null;
    b := n is C<(int, real)>;
    b := n is M<array<bv3>>;

    b := Nil is List<int>;
    b := Nil is List<real>;
    b := List<real>.Nil is List<int>; // error: LHS not assignable to List<int>
    b := List<real>.Nil is List<real>;
    b := Cons(5, Nil) is List<int>;
    b := Cons(5, Nil) is List<real>; // error: LHS not assignable to List<real>
    b := Cons(5.0, Nil) is List<real>;
    b := Cons(5, Nil) is VeryShortList<int>;
    var veryShort: VeryShortList<int> := Nil;
    b := veryShort is List<int>;
    b := veryShort is VeryShortList<real>; // error: LHS not assignable to VeryShortList<real>

    b := From(16) is Stream<int>;
    b := From(16) is Stream<char>; // error: LHS not assignable to Stream<char>

    var f: int -> nat := x => 15;
    b := f is int -> nat;
    b := f is int -> int;
    b := f is nat -> int;
    b := f is nat -> nat;
    b := f is real -> nat; // error: LHS not assignable to type
    b := f is int -> real; // error: LHS not assignable to type
    b := f is int -> Odd; // error: LHS not assignable to type
    b := f is int --> nat;
    b := f is int ~> nat;
    var g: int ~> nat := x => 15;
    b := g is int -> nat;
    b := g is int --> nat;
    b := g is int ~> nat;
    b := g is int ~> real; // error: LHS not assignable to type
    b := g is real --> nat; // error: LHS not assignable to type
  }

  function method From(x: int): Stream<int> {
    More(x, From(x + 1))
  }

  method TypeParametersAreParametric<T, U>(t: T, a: array<T>, obj: object, u: U) {
    var o := t is object; // error: T not assignable to object
    var arr0 := a is array<object>; // error: array<T> not assignable to array<object>
    var arr1 := a is array<int>; // error: array<T> not assignable to array<int>
    var u0 := u is T; // error: U not assignable to T
    var u1 := u is U;
    var u2 := u is object; // error: U not assignable to object
    var u3 := u is object?; // error: U not assignable to object?
    var obj0 := obj is object?;
    var obj1 := obj is object;
    var obj2 := obj is U; // error: object not assignable to U
  }

  trait TraitX { }
  class ClassX extends TraitX { }

  method NonVariant(t0: TraitX, c0: ClassX, at0: array<TraitX>, ac0: array<ClassX>) {
    var t := c0 is TraitX;
    var c := t0 is ClassX;
    var at := ac0 is array<TraitX>; // error: not assignable
    var ac := at0 is array<ClassX>; // error: not assignable
  }
}

module IsRuntimeTestable {
  trait T<X> { }
  // can be reconstructed from a T<X>:
  class C<X0> extends T<X0> { }
  class D<X1> extends T<(int, seq<X1>)> { }
  type E<X2, X3> = D<X2>
  // cannot be reconstructed from a T<X>:
  type F<X2, X3> = d: D<X2> | true witness *
  // can be reconstructed from a T<X>:
  type G<X4, X5> = D<(X4, X5)>
  // cannot be reconstructed from a T<X>:
  type H<X4, X5> = d: D<(X4, X5)> | true witness *
  class I<X6> extends T<int> { }

  method Test0<X>(tx: T<X>, ty: T<(int, seq<X>)>, ti: T<int>, d1: D<X>, d2: D<(X, X)>) returns (b: bool) {
    b := tx is C<X>;
    b := ty is D<X>;
    b := d1 is E<X, X>;
    b := d1 is F<X, X>; // error: cannot be tested at run time, so this is a ghost expression
    b := d2 is G<X, X>;
    b := d2 is H<X, X>; // error: subset types are not tested at run time, so this is a ghost expression
    b := ti is I<X>; // error: cannot be tested at run time, so this is a ghost expression
  }

  method Test1(tx: T<real>, ty: T<(int, seq<real>)>, ti: T<int>, d1: D<real>, d2: D<(real, real)>) returns (b: bool) {
    b := tx is C<real>;
    b := ty is D<real>;
    b := d1 is E<real, real>;
    b := d1 is F<real, real>; // error: cannot be tested at run time, so this is a ghost expression
    b := d2 is G<real, real>;
    b := d2 is H<real, real>; // error: subset types are not tested at run time, so this is a ghost expression
    b := ti is I<real>; // error: cannot be tested at run time, so this is a ghost expression
  }

  // simple synonym
  type Object<Unused> = object

  method Test2(o: object, r: Object<real>, i: Object<int>) returns (b: bool) {
    // these are all okay, because synonyms are just that--synonyms
    b := o is object;
    b := r is object;
    b := i is object;
    b := o is Object<real>;
    b := r is Object<real>;
    b := i is Object<real>;
  }

  // simple subset type
  type TriviallyObject<Unused> = o: object? | o == o

  method Test3(o: object, r: TriviallyObject<real>, i: TriviallyObject<int>) returns (b: bool) {
    b := o is object;
    b := r is object;
    b := i is object;
    b := o is TriviallyObject<real>; // error: cannot be tested at run time, so this is a ghost expression
    b := r is TriviallyObject<real>;
    b := i as object is TriviallyObject<real>; // error: cannot be tested at run time, so this is a ghost expression
  }

  // TODO: also look at any type constraints, to make sure they are testable at run time
}
