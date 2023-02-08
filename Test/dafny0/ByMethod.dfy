// RUN: %exits-with 4 %dafny "%s" > "%t"
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

  ghost predicate P(x: int)

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

module ByMethodRecursion {
  function F(x: int, n: nat): int {
    x
  } by method {
    return if n == 0 then x else F(x, n - 1);
  }

  function G(x: int, n: nat): int {
    x
  } by method {
    return Id(x, n); // error: failure to prove termination
  }
  function Id(x: int, n: nat): int {
    if n == 0 then x else G(x, n - 1)
  }

  function H(x: int, n: nat): int {
    x
  } by method {
    return H(x, n); // error: failure to prove termination
  }

  function I(x: int, n: nat): int {
    if n == 0 then x else J(x, n - 1)
  }
  function J(x: int, n: nat): int {
    x
  } by method {
    return I(x, n); // error: failure to prove termination
  }

  function I'(x: int, n: nat): int
    decreases x, n, 3
  {
    if n == 0 then x else J'(x, n - 1)
  }
  function J'(x: int, n: nat): int {
    x
  } by method {
    return I'(x, n);
  }

  function K(): (k: int) {
    LemmaK(); // error: failure to prove termination
    5
  } by method {
    k := 5;
  }
  lemma LemmaK() {
    var k := K(); // error: failure to prove termination
  }

  function L(): (k: int) {
    5
  } by method {
    LemmaL(); // fine
    k := 5;
  }
  lemma LemmaL() {
    var l := L();
  }

  function M(): (k: int) {
    5
  } by method {
    MethodM(); // error: failure to prove termination
    k := 5;
  }
  method MethodM() {
    var m := M(); // error: failure to prove termination
  }

  function N(): (k: int) {
    5
  } by method {
    MethodN(); // fine
    k := 5;
  }
  method MethodN() {
    ghost var n := N();
  }

  function Func(x: int): int {
    5
  } by method {
    assert Func(x) == 5;
    return 5;
  }

  function Func'(x: int): int {
    5
  } by method {
    var r := Func'(x); // error: failure to prove termination
    return r;
  }
}

module MoreExamples {
  function Fib(n: nat): nat {
    if n < 2 then n else Fib(n - 2) + Fib(n - 1)
  } by method {
    var x, y := 0, 1;
    for i := 0 to n
      invariant x == Fib(i) && y == Fib(i + 1)
    {
      x, y := y, x + y;
    }
    return x;
  }
}
