// RUN: %exits-with 4 %verify --type-system-refresh=true --general-traits=datatype "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module As {
  trait Parent { }
  trait Trait extends Parent { }
  trait TheOther extends Parent { }

  method M<X extends Trait>(x: X) {
    var a0 := x as X;
    var a1 := x as Trait;
    var a2 := x as Parent;
    var a3 := (x as Parent) as TheOther; // error: cannot prove "as TheOther"
  }

  method N<X(==) extends Trait>(x: X) returns (b: bool) {
    var t: Trait := x as Trait;
    if * {
      b := x == t as X; // fine
    } else {
      t := *;
      b := x == t as X; // error: cannot prove the cast, because not every Trait is an X
    }
  }

  method O<Z extends object?>(z: Z) {
    var a := z as object?;
    var b := z as object; // error: cannot verify correctness of cast
  }

  method P<Z extends object>(z: Z) {
    var a := z as object?;
    var b := z as object;
  }
}

module Is {
  trait Parent { }
  trait Trait extends Parent { }
  trait TheOther extends Parent { }

  method M<X extends Trait>(x: X) {
    var a0 := x is X;
    var a1 := x is Trait;
    var a2 := x is Parent;
    var a3 := (x as Parent) is TheOther;

    assert a0 && a1 && a2;
    assert a3; // error: not known if a3 is a TheOther
  }

  method N<X(==) extends Trait>(x: X) returns (ghost b: bool) {
    var t: Trait := x as Trait;
    if * {
      b := t is X;
      assert b;
    } else {
      t := *;
      b := t is X;
      assert b; // error: not every Trait is an X
    }
  }

  method O<Z extends object?>(z: Z) {
    var a := z is object?;
    assert a;
    var b := z is object;
    assert b; // error: assertion not provable
  }

  method P<Z extends object>(z: Z) {
    var a := z is object?;
    var b := z is object;
    assert a && b;
  }
}

module Equality {
  method Eq<Y(==) extends object>(y: Y) returns (b: bool, obj: object) {
    obj := y as object;
    b := y == obj; // both Y and object support equality, so we're good to compare
    assert b;
  }
}

module TypeBoundKnowledge {
  trait Parent { }
  trait XTrait extends Parent { }
  trait YTrait extends Parent { }

  datatype Dt<X extends XTrait> = Dt(x: X)
  {
    method M<Y extends YTrait>(y: Y) {
      var parent: Parent;
      parent := x;
      assert parent is XTrait;
      parent := y;
      assert parent is YTrait;
    }

    function F<Y extends YTrait>(y: Y): int {
      var parentX: Parent := x;
      assert parentX is XTrait;
      var parentY: Parent := y;
      assert parentY is YTrait;
      15
    }

    const K := (x: X) =>
      var parentX: Parent := x;
      assert parentX is XTrait;
      17

    method Negative(xtrait: XTrait) {
      assert xtrait is X; // error
    }
  }

  trait Base<X extends XTrait, W extends XTrait> {
    method M<Y extends YTrait>(z: int, y: Y, x: X, w: W)
      requires z == 5
      requires x is Parent && w is XTrait // this is always true
    twostate function F<Y extends YTrait>(z: int, y: Y, x: X, w: W): int
      requires z == 5
  }

  class XClass extends XTrait { }

  class Class<XX extends XTrait> extends Base<XX, XClass> {
    method M<Y extends YTrait>(z: int, y: Y, x: XX, w: XClass)
      requires z == if y is YTrait then 5 else 7
      requires z == if x is XTrait then 5 else 7
    {
    }
    twostate function F<Y extends YTrait>(z: int, y: Y, x: XX, w: XClass): int
      requires z == if y is YTrait then 5 else 7
      requires z == if x is XTrait then 5 else 7
    {
      17
    }
  }

  class Nope<XX extends XTrait> extends Base<XX, XClass> {
    method M<Y extends YTrait>(z: int, y: Y, x: XX, w: XClass) // error: precondition does not follow from parent trait
      requires z == if y as Parent is YTrait then 100 else 700
    {
    }
    twostate function F<Y extends YTrait>(z: int, y: Y, x: XX, w: XClass): int // error: precondition does not follow from parent trait
      requires z == if y as Parent is XTrait then 100 else 700
    {
      17
    }
  }
}

module Boxing {
  trait Trait extends object { }
  
  method P<Z extends Trait>(z: Z) {
    var a := z as Trait?;
    var b := z as Trait;
    
    var obj: object? := z;
    assert obj is Trait?;
    assert obj is Trait;
  }

  method O<Z extends Trait?>(z: Z) {
    var a := z as Trait?;
    if z as object? != null {
      var b0 := z as Trait;
    }
    var b1 := z as Trait; // error: since z may be null
  }
}

module MoreBoxing {
  trait Trait extends object { }

  method P0<Z extends Trait>(z: Z) returns (obj: object?) {
    obj := z;
    assert true;
  }

  class Cell { var obj: object? }

  method P1<Z extends Trait>(z: Z) returns (c: Cell) {
    c := new Cell;
    c.obj := z;
    assert true;
  }

  method P2<Z extends Trait>(z: Z) returns (obj: array<object?>) {
    obj := new object?[1];
    obj[0] := z as object?; // TODO: this cast should not be needed
    assert true;
  }

  method P3<Z extends Trait>(z: Z) returns (obj: array2<object?>) {
    obj := new object?[1, 1];
    obj[0, 0] := z as object?; // TODO: this cast should not be needed
    assert true;
  }

  datatype Record = Record(obj: object?)

  method P4<Z extends Trait>(z: Z) returns (r: Record) {
    r := Record(z);
    r := r.(obj := z);
    assert true;
  }

  method M<Z extends Trait>(obj: object?, z: Z) returns (r: object?) {
    return z;
  }

  method P5<Z extends Trait>(z: Z) returns (obj: object?) {
    obj := M(z, z);
    assert true;
  }

  function F(obj: object?): int { 4 }

  method P6<Z extends Trait>(z: Z) returns (u: int) {
    u := F(z);
    assert true;
  }

  method P7<Z extends Trait>(z: Z) returns (u: int) {
    u := var obj: object? := z;
      assert obj == null || obj != null;
      14;
    assert true;
  }

  method P8<Z extends Trait>(z: Z, t: Trait) returns (s: seq<Trait>) {
    s := [z];
    s := [z as Trait, t]; // TODO: this cast should not be needed
    s := s[0 := z];
    assert s[0] == z as Trait;
    assert z in s;
    assert !(z !in s);
    assert true;
  }

  method P9<Z(==) extends Trait>(z: Z, t: Trait) returns (m: map<Trait, Trait>, mi: map<Trait, Trait>) {
    m := map[z := z];
    m := m[z as Trait := z as Trait]; // TODO: these casts should not be needed
    mi := map[z := z];
    mi := mi[z as Trait := z as Trait]; // TODO: these casts should not be needed

    m := map[z as Trait := t];
    m := m[z as Trait := t];
    mi := map[z as Trait := t];
    mi := mi[z as Trait := t];

    m := map[t := z as Trait];
    m := m[t := z as Trait];
    mi := map[t := z as Trait];
    mi := mi[t := z as Trait];

    if t == z as Trait {
      assert z in m;
      assert !(z !in m);
      assert z in mi;
      assert !(z !in mi);
    }
  }

  method P10<Z(==) extends Trait>(z: Z, t: Trait) returns (m: multiset<Trait>) {
    m := multiset{z, z};
    m := multiset{z as Trait, t}; // TODO: this cast should not be needed
    m := m[z as Trait := 13]; // TODO: this cast should not be needed
    assert z in m;
    assert !(z !in m);
  }

  method P11<Z(==) extends Trait>(z: Z, t: Trait) returns (s: set<Trait>, si: iset<Trait>) {
    s := {z};
    s := {z as Trait, t}; // TODO: this cast should not be needed
    assert z in s;
    assert !(z !in s);

    si := iset{z};
    si := iset{z as Trait, t}; // TODO: this cast should not be needed
    assert z in si;
    assert !(z !in si);
  }

  method P12<Z(==) extends Trait>(z: Z, t: Trait) returns (s: set<Trait>, si: iset<Trait>) {
    var A := {z};
    var B := {z as Trait, t};
    s := set u: Trait | u in A;
    s := set u: Trait | u in B; // TODO: this cast should not be needed
    si := iset u: Trait | u in A;
    si := iset u: Trait | u in B; // TODO: this cast should not be needed
  }

  method P14<Z(==) extends Trait>(z: Z, t: Trait) {
    assert allocated(z);
  }

  method P15<Z(==) extends Trait>(s: set<Z>)
    modifies s as set<Trait>
  {
  }

  function F16<Z(==) extends Trait>(s: set<Z>): int
    reads s as set<Trait>
  {
    10
  }
}

module TestThatOverrideCheckHasEnoughInformationAboutTypeBounds {
  trait TrTrParent { }
  trait TrTr extends TrTrParent { }

  trait Parent extends object {
    function F<W extends TrTr>(u: nat, w: W): W
      requires u % 5 == 0
      reads this
      ensures w == w

    method M<W extends TrTr>(u: nat, w: W) returns (wo: W)
      requires u % 5 == 0
      modifies this
      ensures w == wo
  }

  class Cell extends Parent {
    var data: int

    function F<W extends TrTr>(u: nat, w: W): W
      requires u % 5 == 0
      requires w as TrTrParent is TrTr // the proof that this condition is "true" requires the type-bound axioms
      reads this
      ensures w == w
    {
      var m := u + data;
      var o := 2 * if m < 0 then -m else m;
      w
    }

    method M<W extends TrTr>(u: nat, w: W) returns (wo: W)
      requires u % 5 == 0
      modifies this
      ensures wo as TrTrParent is TrTr ==> wo == w
    {
      return w;
    }
  }
}

module Variance {
  class Generic<X> { }
  datatype Covariant<+X> = Make(value: X)

  method TestAutoConversions()
  {
    var g: Generic<int> := new Generic<int>;
    var h: Generic<nat> := new Generic<nat>;
    if * {
      g := h; // error: non-compatible types
    } else {
      h := g; // error: non-compatible types
    }
  }

  method TestExplicitConversions()
  {
    var g: Generic<int> := new Generic<int>;
    var h: Generic<nat> := new Generic<nat>;
    if * {
      g := h as Generic<int>; // error: non-compatible types
    } else {
      h := g as Generic<nat>; // error: non-compatible types
    }
  }

  method TestCovariance() {
    var g: Covariant<int> := Covariant<int>.Make(5);
    var h: Covariant<nat> := Covariant<nat>.Make(5);
    if * {
      g := h;
      g := h as Covariant<int>; // (legacy error)
    } else {
      h := g;
      h := g as Covariant<nat>; // (legacy error)
    }
  }
}

module BadBounds {
  trait ReferenceTrait extends object {
    const u: int
  }

  type ConstrainedReferenceTrait = r: ReferenceTrait | r.u < 100 witness *

  method P<R extends ReferenceTrait?, S extends ReferenceTrait, T extends ConstrainedReferenceTrait>(r: R, s: S, t: T) { }

  method PCaller(r: ReferenceTrait?, s: ReferenceTrait, t: ConstrainedReferenceTrait) {
    P<ReferenceTrait?, ReferenceTrait, ConstrainedReferenceTrait>(r, s, t);
    P<ReferenceTrait?, ReferenceTrait, ConstrainedReferenceTrait>(t, t, t);
    // The following errors are ordinary parameter-type-mismatch errors; the explicit type arguments do satisfy their required bounds
    P<ReferenceTrait?, ReferenceTrait, ConstrainedReferenceTrait>(s, s, s); // error: argument 2 is not a ConstrainedReferenceTrait
    P<ReferenceTrait?, ReferenceTrait, ConstrainedReferenceTrait>(r, r, t); // error: argument 1 is not a ReferenceTrait
    P<ReferenceTrait?, ReferenceTrait, ConstrainedReferenceTrait>(r, s, r); // error: argument 2 is not a ConstrainedReferenceTrait
  }

  trait GoodTrait { }

  class E extends GoodTrait { }

  method Q<G extends GoodTrait>(g: G) { }

  method QCaller(e: E, eMaybe: E?) {
    Q<E>(e);
    Q<E>(eMaybe); // error: eMaybe may be null
  }
}
