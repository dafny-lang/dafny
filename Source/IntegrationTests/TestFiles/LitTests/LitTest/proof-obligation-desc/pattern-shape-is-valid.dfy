// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = D0(n: nat) | D1

method F(d: D) {
  assert d.D0?;
  var D0(n) := d;
}