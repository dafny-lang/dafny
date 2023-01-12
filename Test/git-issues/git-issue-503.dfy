// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Option {
  datatype t<A> = None | Some(A)
}

module P {
  datatype t = P
}

module Bug {
  import Option
  import P
  datatype input = Input(z: Option.t<P.t>)
  type t = input -> bool
  const Foo: t := (x: input) =>
    match x
      case Input(Some(_)) => true
}

module OK {
  import Option
  import P
  datatype input = Input(z: Option.t<P.t>)
  type t = input -> bool
  const Foo: t := (x: input) =>
    match x
      case Input(Some(_)) => true
      case Input(None) => true
}

