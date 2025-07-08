// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(x: int)

trait T {
  function F(i: int): int
    requires i < 10
    ensures F(i) < 5
    ensures P(F(i))
}

trait T' extends T {
  function F(i': int): int
    requires i' < 5
    requires P(i')
    ensures F(i') < 10
  {
    0
  }
}