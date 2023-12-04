// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint16 = x | 0 <= x < 0x1_0000
datatype D = A | B

method M(x: D, u: uint16) returns (r: uint16) {
  var v := 5;
  match x {
    case A => r := 12;
    case B => r := 13;
  }
  r := v;
}
