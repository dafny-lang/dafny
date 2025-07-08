// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = D0(n: nat) | D1 | D2(b: bool, n: nat)

method F(d: D) {
  var d' := d.(n := 0);
}