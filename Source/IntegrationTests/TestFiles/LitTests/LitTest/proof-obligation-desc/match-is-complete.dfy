// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = D0 | D1

function F(d: D): D {
  match d
    case D0 => D1
}