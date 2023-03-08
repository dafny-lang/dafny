// RUN: %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint16 = x | 0 <= x < 0x1_0000
datatype D = A | B

ghost function F(x: D): uint16 {
  match x
  case A => 12
  case B => 13
}
