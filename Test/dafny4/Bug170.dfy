// RUN: %baredafny verify %args --print-tooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module InductiveThings {
  predicate P(x: int)
  predicate Q(x: int)

  least predicate A(x: int)
  {
    P(x) || B(x+1)
  }

  least predicate B(x: int)
  {
    Q(x) || A(x+1)
  }

  least lemma AA(x: int)  // should be specialized not just for A, but also for B, which is in the same strongly connected component as A in the call graph
    requires A(x)
  {
    if B(x+1) {  // this one should be replaced by B#[_k-1](x+1)
      BB(x+1);
    }
  }

  least lemma BB(x: int)  // should be specialized not just for B, but also for A, which is in the same strongly connected component as B in the call graph
    requires B(x)
  {
    if A(x+1) {  // this one should be replaced by A#[_k-1](x+1)
      AA(x+1);
    }
  }
}

module CoThings {
  greatest predicate A(x: int)
  {
    B(x+1)
  }

  greatest predicate B(x: int)
  {
    A(x+1)
  }

  greatest lemma AA(x: int)  // should be specialized not just for A, but also for B, which is in the same strongly connected component as A in the call graph
    ensures A(x)
  {
    BB(x+1);
    assert B(x+1);  // this one should be replaced by B#[_k-1] (which will happen, provided that AA is listed as also being specialized for B)
  }

  greatest lemma BB(x: int)  // should be specialized not just for B, but also for A, which is in the same strongly connected component as B in the call graph
    ensures B(x)
  {
    AA(x+1);
    assert A(x+1);  // this one should be replaced by A#[_k-1] (which will happen, provided that BB is listed as also being specialized for A)
  }
}

module SingleThings {
  predicate P(x: int)

  least predicate A(x: int)
  {
    P(x) || A(x+1)
  }

  least lemma AA(x: int)  // should be specialized just for A
    requires A(x)
  {
    if A(x+1) {  // this one should be replaced by B#[_k-1](x+1)
      AA(x+1);
    }
  }
}
