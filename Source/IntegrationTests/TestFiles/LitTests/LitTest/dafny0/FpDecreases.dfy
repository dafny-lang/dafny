// RUN: %testDafnyForEachResolver "%s"

// An fp32/fp64 component in a decreases clause, which needs an arm in ComputeLessEq. fp32/fp64 are
// finite carriers, so -- as for bitvectors and char -- any strict order on them is well founded and
// no lower-bound conjunct is needed. The order is total, so NaN needs no separate case: it is the
// largest value, and a metric can no more increase to it than to any other larger one.

// The metric may be NaN, the order being total.
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

// The loop path reaches DecreasesCheck without going through CompatibleDecreasesTypes, so it needs
// covering independently of the function path.
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
// NaN, since less(0.0, NaN) holds. Still well founded: one step, and NaN cannot be re-entered, that
// being an increase.
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

// The converse must not verify: ascending to NaN is an increase like any other. Rejected loops live
// in FpUnsoundLoopAndDivision.dfy, this file expecting a clean exit code.
