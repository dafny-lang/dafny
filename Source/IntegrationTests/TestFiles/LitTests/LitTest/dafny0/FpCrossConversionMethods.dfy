// RUN: %testDafnyForEachResolver "%s"

// fp32.FromFp64 rounds to nearest, ties to even: the rounding counterpart of 'as fp32', which
// instead asserts exact representability. '~' applies only to literals, so this is the only way to
// write a rounding narrowing conversion, and like the rest of the family it carries no obligation.
//
// It needs its own case in TrExprSpecialFunctionCall; the generic tail emits an undeclared Boogie
// function.
//
// No widening counterpart: fp32 -> fp64 is exact for every input, so
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
