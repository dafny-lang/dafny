// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = D0 | D1

method F(d: D) returns (res: D) {
  if {
    case d == D0 => return D1;
  }
}