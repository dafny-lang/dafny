// RUN: %testDafnyForEachResolver "%s"

// An fp32/fp64 component in a decreases clause used to abort translation (exit 134) at the
// Contract.Assert in ComputeLessEq, which had no floating-point arm. fp32/fp64 are finite
// carriers, so -- exactly as for bitvectors and char -- any strict order on them is well
// founded and no lower-bound conjunct is needed. "less" is IEEE fp.lt and "eq" is structural
// equality, so a NaN metric simply never decreases and the two zeros are neither eq nor less.

function CountDown(x: fp64, n: nat): nat
  requires !x.IsNaN
  decreases x, n
{
  if n == 0 then 0 else CountDown(x, n - 1)
}

function Descend(x: fp32, n: nat): nat
  decreases n, x
{
  if n == 0 then 0 else Descend(x, n - 1)
}

// Exercises the loop path, which reaches DecreasesCheck without going through
// CompatibleDecreasesTypes and so crashed independently of the function path.
// The decrease is kept trivial on purpose: metrics built from fp arithmetic (z - 1.0, z / 2.0)
// are a known incompleteness -- Z3 times out on them even where they do decrease, and above
// 2^53 they genuinely do not decrease at all, since x - 1.0 == x there.
method LoopWithFpMetric(y: fp64) returns (steps: nat)
  requires !y.IsNaN
{
  steps := 0;
  var z := y;
  while z > 1.0
    decreases z
  {
    z := 0.0;
    steps := steps + 1;
  }
}
