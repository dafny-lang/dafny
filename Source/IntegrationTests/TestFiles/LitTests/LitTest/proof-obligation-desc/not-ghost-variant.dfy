// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = ghost G0 | ghost G1 | C0 | C1

method NotGhostVariantDiscriminator(d: D) returns (res: nat) {
  res := 0;
  if d.C0? {
    res := 1;
  }
}

method NotGhostVariantEquality(d: D) returns (res: nat) {
  res := 0;
  if d == d {
    res := 1;
  }
}