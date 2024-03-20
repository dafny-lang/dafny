// RUN: %exits-with 4 %verify --type-system-refresh --general-traits=datatype "%s" > "%t"
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
