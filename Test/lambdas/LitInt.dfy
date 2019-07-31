// RUN: %dafny /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const N: nat

function Fibonacci(n: int): int
{
	if n <= 1 then 1
	else Fibonacci(n - 2) + Fibonacci(n - 1)
}

// The following assertion should fail.
// Specifically, the verifier should not attempt to
// prove that for all N, Fibonacci is not equal to 143
// since that would not terminate. In order to avoid that
// we do not wrap `const`s in `Lit`s. If we did wrap this
// `N` in a `Lit` the verifier would keep trying to prove this
// assertion.
function Wrong(): bool {
	assert Fibonacci(N) != 143; // should fail
	true
}
