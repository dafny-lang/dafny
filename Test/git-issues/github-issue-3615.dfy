// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Foo(x: int := 3): int {
   x
}

datatype Zee = Kwa | Zam

function Zaz(x: Zee): int {
  match x {
    case Kwa => Foo()
    case _ => Foo()
  }
}
