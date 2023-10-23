// RUN: %exits-with 2 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  type SubsetType<X> = x: int | true

  method M() {
    var s: SubsetType; // error: type argument underspecified
    s := 3;
  }

  datatype Record<U> = Record(SubsetType<U>)

  method P(r: Record<real>) {
    match r
    case Record(s: SubsetType) => // error: type argument underspecified
  }
}

module B {
  class Clx { }
  type MyClx<U> = c: Clx | true witness *

  datatype Datatype = DX | DY(o: object)

  ghost function M0<U>(dt: Datatype): int
    requires dt.DX?
  {
    match dt
    case DX => 2
    case DY(o: MyClx<U>) => 3 // error: type object not assignable to type MyClx<U>
  }

  datatype Datatype'<U> = DX' | DY'(o: MyClx<U>)

  ghost function M1<U>(dt: Datatype'<U>): int
  {
    match dt
    case DX' => 2
    case DY'(o: object) => 3
  }

  datatype Datatype'' = DX'' | DY''(o: Clx)

  ghost function M2<U>(dt: Datatype''): int
  {
    match dt
    case DX'' => 2
    case DY''(o: MyClx<U>) => 3
  }
}

module C {
  class Clx { }
  type MyClx<U> = c: Clx | true witness *
  datatype Datatype'' = DX'' | DY''(o: Clx)

  ghost function M3<U>(dt: Datatype''): int
  {
    match dt
    case DX'' => 2
    case DY''(o: MyClx) => 3 // error: type argument cannot be inferred -- underspecified
  }
}

module D {
  datatype NatRec = NatRec(n: nat)

  function F(r: NatRec): int {
    match r
    case NatRec(x: int) =>
      var y: int := x;
      var m: nat := y;
      m
  }

  datatype IntRec = IntRec(n: int)

  function G(r: IntRec): nat
    requires 0 <= r.n
  {
    match r
    case IntRec(x: nat) =>
      var y: nat := x;
      var m: int := y;
      m
  }
}
