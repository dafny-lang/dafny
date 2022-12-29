// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Methods_EverythingGoes {
  predicate R<Y>(y: Y) { true }

  type Opaque(==)
  type OpaqueNoAlloc(!new)

  class Cell {
    var data: int
  }

  datatype List<G> = Nil | Cons(G, List<G>)

  method M0()
    requires forall x: Opaque :: R(x)  // borderline: may seem innocent enough, but it quantifies over all Opaque

  method M0'()
    requires forall x: Opaque :: allocated(x) ==> R(x)  // fine

  method M0''()
    requires forall x: OpaqueNoAlloc :: R(x)  // fine

  method E0()
    requires exists x: Opaque :: R(x)  // borderline: may seem innocent enough, but it quantifies over all Opaque

  method M1<X>()
    requires forall x: X :: R(x)  // borderline: may seem innocent enough, but it quantifies over all X

  method E1<X>()
    requires exists x: X :: R(x)  // borderline: may seem innocent enough, but it quantifies over all X

  method E2<X(!new)>()
    requires exists x: X :: R(x)  // fine

  method M2()
    requires forall c: Cell :: R(c)  // borderline: quantifies over all references

  method M2'(S: set<Cell>)
    requires forall c: Cell :: c in S ==> R(c)  // fine

  method M3()
    requires forall xs: List<nat> :: R(xs)  // fine (no issues of allocation here)

  method M4()
    requires forall xs: List<Cell> :: R(xs)  // borderline: involves references

  method M4'(S: set<List<Cell>>)
    requires forall xs: List<Cell> :: xs in S ==> R(xs)  // fine

  method M5<H>()
    requires forall xs: List<H> :: R(xs)  // borderline: may involved allocation state

  method M5'<H(==)>(S: set<List<H>>)
    requires forall xs: List<H> :: xs in S ==> R(xs)  // fine

  method M6()
    requires forall xs: List<Opaque> :: R(xs)  // borderline: may involved allocation state

  method M6'(S: set<List<Opaque>>)
    requires forall xs: List<Opaque> :: xs in S ==> R(xs)  // fine
}

module Functions_RestrictionsApply {
  predicate R<Y>(y: Y) { true }

  type Opaque(==)

  class Cell {
    var data: int
  }

  datatype List<G> = Nil | Cons(G, List<G>)

  predicate M0()
  {
    forall x: Opaque :: R(x)  // error: may seem innocent enough, but it quantifies over all Opaque
  }

  predicate E0()
  {
    exists x: Opaque :: R(x)  // error: may seem innocent enough, but it quantifies over all Opaque
  }

  predicate M1<X>()
  {
    forall x: X :: R(x)  // error: may seem innocent enough, but it quantifies over all X
  }

  predicate E1<X>()
  {
    exists x: X :: R(x)  // error: may seem innocent enough, but it quantifies over all X
  }

  predicate M2()
  {
    forall c: Cell :: R(c)  // error: quantifies over all references
  }

  predicate M2'(S: set<Cell>)
  {
    forall c: Cell :: c in S ==> R(c)  // fine
  }

  predicate M3()
  {
    forall xs: List<nat> :: R(xs)  // fine (no issues of allocation here)
  }

  predicate M4()
  {
    forall xs: List<Cell> :: R(xs)  // error: involves references
  }

  predicate M4'(S: set<List<Cell>>)
  {
    forall xs: List<Cell> :: xs in S ==> R(xs)  // fine
  }

  predicate M5<H>()
  {
    forall xs: List<H> :: R(xs)  // error: may involved allocation state
  }

  predicate M5'<H>(S: set<List<H>>)
  {
    forall xs: List<H> :: xs in S ==> R(xs)  // fine
  }

  predicate M6()
  {
    forall xs: List<Opaque> :: R(xs)  // error: may involved allocation state
  }

  predicate M6'(S: set<List<Opaque>>)
  {
    forall xs: List<Opaque> :: xs in S ==> R(xs)  // fine
  }
}

module OtherComprehensions {
  predicate R<Y>(y: Y) { true }

  type Opaque(==)
  type OpaqueNoAlloc(!new)

  class Cell {
    var data: int
  }

  datatype List<G> = Nil | Cons(G, List<G>)

  method M0() {
    assert {} == set o: Opaque | R(o);  // error (x2): may be infinite, and depends on alloc
  }

  method M1() {
    if
    case true =>
      assert iset{} == iset o: Opaque | R(o);  // borderline: o depends on alloc
    case true =>
      assert iset{} == iset o: Opaque | allocated(o) && R(o);  // fine
      assert {} == set o: Opaque | allocated(o) && R(o);  // this is also finite
    case true =>
      assert iset{} == iset o: OpaqueNoAlloc | R(o);  // fine
  }

  function F0(): int
    requires iset{} == iset o: Opaque | R(o)  // error: may involve references
  {
    15
  }

  function F1(): int
    requires iset{} == iset n: nat | R(n)  // fine
  {
    15
  }

  function F2<G>(): int
    requires iset{} == iset xs: List<G> | R(xs)  // error: may involve references
  {
    15
  }

  function H0<G>(): (s: iset<List<G>>)
    ensures s == iset xs: List<G> | R(xs)  // error: may involve references
  {
    iset{}
  }

  function K0<G>(c: Cell): int
    reads if iset{} == iset xs: List<G> | R(xs) then {c} else {}  // error: may involve references
  {
    15
  }
}

module CompiledComprehensions {
  predicate method R<Y>(y: Y) { true }

  type OpaqueNoAlloc(!new)
    
  method M2() returns (s: iset<OpaqueNoAlloc>) {
    s := iset o: OpaqueNoAlloc | R(o);  // error: not compilable (too awkward)
  }
}

module Allocated0 {
  class Cell {
    var data: int
  }

  method M0() {
    assert forall c: Cell :: c.data < 100;  // borderline: depends on alloc
  }

  method M1() {
    assert forall c: Cell :: allocated(c) ==> c.data < 100;
  }

  method N0() returns (s: set<Cell>) {
    s := set c: Cell | c.data < 100;  // error: this involves the allocated state
  }

  method N1() returns (s: set<Cell>) {
    s := set c: Cell | allocated(c) && c.data < 100;  // error: finite, but not (comfortably) compilable
  }

  ghost method N2() returns (s: set<Cell>) {
    s := set c: Cell | allocated(c) && c.data < 100;  // fine: this is finite and need not be compiled
  }
}

module Allocated1 {
  class Cell {
    var data: int
  }

  function F(): set<Cell> {
    set c: Cell | allocated(c) && c.data < 100  // error: function not allowed to depend on allocation state
  }

  function A(c: Cell): bool
  {
    allocated(c)  // error: function not allowed to depend on allocation state
  }

  twostate function TS0(c: Cell, new d: Cell): bool
  {
    allocated(d)  // error: even though this is always true, it is not allowed (when the function definition axiom
                  // is applied in a reachable heap, but that's not guaranteed)
  }

  twostate function TS1(c: Cell, new d: Cell): bool
  {
    allocated(d)  // error: even though this is always true, it is not allowed (when the function definition axiom
                  // is applied in a reachable heap, but that's not guaranteed)
  }

  twostate function TS2(c: Cell, new d: Cell): bool
  {
    old(allocated(d))  // this value depends on the pre-state, but it's allowed in any case because the pre-state is non-variant in the frame axiom
  }

  twostate function TS3(c: Cell, new d: Cell): bool
  {
    fresh(d)  // this value depends on the pre-state, but it's allowed in any case because the pre-state is non-variant in the frame axiom
  }
}

module FiniteBecauseOfType {
  method M() {
    ghost var s := set x: int | true :: false;  // this denotes a finite set, because the argument type is bool
    ghost var m := map x: int | true :: true := 6;  // this denotes a finite map, because the key type is bool
    var s'; s' := set x: int | true :: false;  // error: although this is a finite set, it's not clear it can be computed in finite time
    var m'; m' := map x: int | true :: true := 6;  // error: ditto
  }
}

module WithoutOlder {
  datatype List<T> = Nil | Cons(T, List<T>)

  predicate ElementsContainedIn<X>(xs: List<X>, S: set<X>) {
    match xs
    case Nil => true
    case Cons(x, tail) => x in S && ElementsContainedIn(tail, S)
  }

  function Collection<X>(S: set<X>): iset<List<X>> {
    iset zs: List<X> | ElementsContainedIn(zs, S) // error: needs 'older zs' for ElementsContainedIn
  }
}

module WithOlder {
  datatype List<T> = Nil | Cons(T, List<T>)

  // For a proof the 'older' in the following line, see OlderVerification.dfy.
  predicate ElementsContainedIn<X>(older xs: List<X>, S: set<X>) {
    match xs
    case Nil => true
    case Cons(x, tail) => x in S && ElementsContainedIn(tail, S)
  }

  function Collection<X>(S: set<X>): iset<List<X>> {
    iset zs: List<X> | ElementsContainedIn(zs, S)
  }
}
