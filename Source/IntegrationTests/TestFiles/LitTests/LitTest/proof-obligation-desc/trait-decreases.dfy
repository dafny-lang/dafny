// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T {
  method M0(x: nat, y: bool) decreases x, y
  method M1(x: nat, y: bool) decreases y, x
  method M2(x: nat, y: bool) decreases false, x
}

class C extends T {
  method M0(x: nat, y: bool) decreases y, x
  { }
  method M1(x: nat, y: bool) decreases y
  { }
  method M2(x: nat, y: bool) decreases y, x
  { }
}