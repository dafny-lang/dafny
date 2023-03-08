// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file contains the automatic proofs of two nice properties about Fibonacci-like numbers.
// The theorems were inspired by singingbanana's video https://www.youtube.com/watch?v=CWhcUea5GNc.
//
// The attempt to prove them discovered issue 1250, for which this file contains regression tests.
// In particular, the proof obligations marked with a (*) below did not verify before the issue-1250 fix.

const A: int
const B: int

ghost function Fib(n: nat): int {
  if n == 0 then A
  else if n == 1 then B
  else Fib(n - 2) + Fib(n - 1)
}

// Sum f(i) for i from 0 through n (inclusive)
ghost function Sum(n: nat, f: nat -> int): int {
  f(n) + if n == 0 then 0 else Sum(n - 1, f)
}

lemma Eleven()
  ensures Sum(9, Fib) == 11 * Fib(6)
{
}

lemma FibSum(n: nat)
  ensures Sum(n, Fib) == Fib(n + 2) - Fib(1) // (*)
{
}

lemma {:induction false} FibSumManual(n: nat)
  ensures Sum(n, Fib) == Fib(n + 2) - Fib(1) // (*)
{
  if n == 0 {
  } else {
    calc {
      Sum(n, Fib);
    ==  // def. Sum
      Fib(n) + Sum(n - 1, Fib);
    ==  { FibSumManual(n - 1); }
      Fib(n) + Fib(n - 1 + 2) - Fib(1);
    ==
      Fib(n) + Fib(n + 1) - Fib(1);
    ==  // def. Fib
      Fib(n + 2) - Fib(1);
    }
    assert Sum(n, Fib) == Fib(n + 2) - Fib(1); // (*)
    assert Sum(n, Fib) == Fib(n + 2) - Fib(1); // (*)

    assert Sum(n, Fib) == Sum(n, Fib);
  }
  assert Sum(n, Fib) == Fib(n + 2) - Fib(1); // (*)
}
