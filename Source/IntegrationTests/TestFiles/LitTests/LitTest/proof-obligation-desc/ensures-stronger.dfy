// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(i: int)
predicate Q(i: int)

trait T {
  method M(b: bool)
    returns (res: int)
    ensures P(res)
    ensures P(res + 1)
    ensures b ==> Q(res)
}

class C extends T {
  method M(b': bool)
    returns (res': int)
    ensures P(res')
  {
    assume {:axiom} P(0);
    return 0;
  }
}