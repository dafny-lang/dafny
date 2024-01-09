// RUN: %exits-with 2 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  datatype Record = Record(o: object)

  class C { }

  method M(r: Record)
    requires r.o is C
  {
    match r
    case Record(c: C) => // error: not allowed to down-cast from a trait in case pattern
  }
}

module B {
  class Clx { }
  type MyClx<U> = c: Clx | true witness *

  datatype Datatype = DX | DY(o: object)

  function F<U>(dt: Datatype): int
    requires dt.DX?
  {
    match dt
    case DX => 2
    case DY(o: MyClx<U>) => 3 // error: not allowed to down-cast from a trait in case pattern
  }

  method P<U>(dt: Datatype)
    requires dt.DX?
  {
    match dt
    case DX =>
    case DY(o: MyClx<U>) => // error: not allowed to down-cast from a trait in case pattern
  }
}

module C {
  class Clx<W> { }
  type MyClx<U> = c: Clx<U> | true witness *

  datatype Datatype = DX | DY(o: object)

  function F<U>(dt: Datatype): int
    requires dt.DX?
  {
    match dt
    case DX => 2
    case DY(o: MyClx<U>) => 3 // error: not allowed to down-cast from a trait in case pattern
  }

  method P<U>(dt: Datatype)
    requires dt.DX?
  {
    match dt
    case DX =>
    case DY(o: MyClx<U>) => // error: not allowed to down-cast from a trait in case pattern
  }
}
