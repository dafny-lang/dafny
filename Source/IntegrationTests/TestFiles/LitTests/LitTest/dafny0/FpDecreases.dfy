// RUN: %testDafnyForEachResolver "%s"

// An fp32/fp64 component in a decreases clause used to abort translation (exit 134) at the
// Contract.Assert in ComputeLessEq, which had no floating-point arm. fp32/fp64 are finite
// carriers, so -- exactly as for bitvectors and char -- any strict order on them is well
// founded and no lower-bound conjunct is needed. "less" is Dafny's fp order, which is a strict
// total order on the whole carrier, so there is no NaN case to reason about separately: NaN is
// simply the largest value, and a metric can no more increase to it than to any other larger one.

// No precondition needed: the metric may be NaN, since the order is total.
function CountDown(x: fp64, n: nat): nat
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

// NaN being the maximum rather than incomparable is observable here: a metric may descend OUT of
// NaN. Under the earlier partial order this loop did not verify, because less(0.0, NaN) was false.
// It is still well founded -- one step, and NaN cannot be re-entered, since that would be an
// increase.
method LoopDescendingOutOfNaN() returns (steps: nat) {
  steps := 0;
  var z := fp64.NaN;
  while z.IsNaN
    decreases z
  {
    z := 0.0;
    steps := steps + 1;
  }
}

// The converse does not verify, and must not: ascending to NaN is an increase like any other. The
// loop is deliberately absent rather than commented as an expected error, because this file expects
// a clean exit code; FpUnsoundLoopAndDivision.dfy is where rejected loops live.
