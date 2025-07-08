// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(i: int)
predicate Q(i: int)

trait T {
  method M(i: int)
    returns (res: bool)
    requires P(i)
    requires Q(i)
}

class C extends T {
  method M(i': int)
    returns (res': bool)
    requires P(i')
    requires Q(i' * 2)
    requires P(i' + 1) ==> Q(i' + 1)
  {
    res' := true;
  }
}