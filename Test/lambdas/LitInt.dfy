// RUN: %exits-with 4 %dafny /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const N: nat
const M := 12;

ghost function Fibonacci(n: int): int
{
  if n < 2 then n
  else Fibonacci(n - 2) + Fibonacci(n - 1)
}

ghost function Wrong(): bool
{
  // The following assertion should fail.
  // Specifically, the verifier should not attempt to
  // prove that for all N, Fibonacci is not equal to 143
  // since that would not terminate. In order to avoid that
  // we do not wrap `const`s in `Lit`s. If we did wrap this
  // `N` in a `Lit` the verifier would keep trying to prove this
  // assertion.
  assert Fibonacci(N) != 143; // should fail

  // Should pass
  assert Fibonacci(M) == 144;

  // Should fail: constants are not Lit-wrapped
  // and therefore the sum "M + 5" is not a Lit,
  // so Fibonacci(M+5) cannot be evaluated without a fuel
  // (but as shown below in `CheckFib` the verifier knows that
  // Fibonacci(17) == 1597)
  assert Fibonacci(M + 5) == 1597;
  true
}

lemma CheckFib()
  ensures Fibonacci(17) == 1597 {}
