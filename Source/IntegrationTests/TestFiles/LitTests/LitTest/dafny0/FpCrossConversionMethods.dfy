// RUN: %testDafnyForEachResolver "%s"

// fp32.FromFp64 used to abort translation with
// "use of undeclared function: _System.fp32.FromFp64", because the fp arm of
// TrExprSpecialFunctionCall had no case for it and fell through to the generic tail.
//
// It rounds to nearest, ties to even, and is the rounding counterpart of 'as fp32', which
// instead asserts exact representability. Since '~' applies only to literals, it is the only
// way to write a rounding narrowing conversion, so like the rest of the unchecked family it
// carries no proof obligation.
//
// There is deliberately no widening counterpart: fp32 -> fp64 is exact for every input, so
// 'x as fp64' is unconditional and a method would only duplicate it.

lemma WideningNeedsNoMethod(x: fp32) {
  var widened := x as fp64;      // exact, no obligation
  assert widened == x as fp64;
}

lemma NarrowingOverflowsToInfinity() {
  assert fp32.FromFp64(fp64.MaxValue).IsInfinite;
}

lemma NarrowingCarriesNoExactnessObligation(x: fp64) {
  // Unlike 'x as fp32', this needs no proof that x is exactly representable as fp32.
  var narrowed := fp32.FromFp64(x);
  assert narrowed == fp32.FromFp64(x);
}
