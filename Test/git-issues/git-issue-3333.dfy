// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint16 = x: int | 0 <= x < 0x1_0000

datatype Datatype = A | B
{
  function method Foo(): uint16 {
    match this
    case A => 1
    case B => 2
  }
}
