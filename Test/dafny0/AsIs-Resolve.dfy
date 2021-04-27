// RUN: %dafny /compile:0 "%s" > "%t"
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
