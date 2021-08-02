// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module ByMethodVerification {
  function F(x: nat): int {
    x
  } by method {
    var j := 0;
    for i := 0 to x
      invariant i == -j
    {
      j := j - 1;
    }
    return -j;
  }

  function G(x: nat): (r: int) {
    x
  } by method {
    var j := 0;
    for i := 0 to x
      invariant i == -j
    {
      j := j - 1;
    }
    if * {
      return -j;
    } else {
      r := -j;
    }
  }

  function H(x: nat): (r: int) {
    x
  } by method {
    var j := 0;
    for i := 0 to x
      invariant i == -j // error: body does not maintain invariant
    {
      j := j - 2;
    }
    return j; // error: does not live up to method postcondition
  }

  predicate P(x: int)

  function V0(x: int): (r: int) // error: function body does not meet postcondition
    ensures P(r)
  {
    x
  } by method {
    return x; // this is fine, because it does what the function body does
  }

  function V1(x: int): (r: int) // error: function body does not meet postcondition
    ensures P(r)
  {
    x
  } by method {
    return x + 1; // error: this is not what the function body does
  }

  predicate Pred0(x: int) // error: function body does not meet postcondition
    ensures Pred0(x) ==> x < 100
  {
    x == 23 || x == 102
  } by method {
    return x == 22; // error: this is not what the function body does
  }

  predicate Pred1(x: int) // error: function body does not meet postcondition
    ensures Pred1(x) ==> x < 100
  {
    x == 23 || x == 102
  } by method {
    // Because the function body and function postcondition are at odds with each
    // other for x==102, the verifier finds x==102 to be absurd. Therefore, the
    // verifier has no complaints about the following implementation:
    return x == 23; // since the consequence axiom says
  }
}
