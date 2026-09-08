// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

// A compiled literal must be the same value the verifier reasoned about. The verifier holds the exact
// rounded value while the generated code holds a decimal, and a decimal one digit short names the
// neighbouring float -- BigFloat.ToDecimalString prints 0.5714285714285713 for the fp64 nearest 4/7.
// Literals are therefore emitted as the shortest round-trip decimal, read back, and compared against
// the resolver's value before being written out.
//
// The pairs below are adjacent floats whose shortest decimals differ only in the last digit, so any
// rounding or shortening on the way to the generated code collapses a pair onto one value and makes
// the assert and the print disagree.

method AdjacentFp64Literals() {
  var a: fp64 := ~0.5714285714285714;
  var b: fp64 := ~0.5714285714285713;
  assert a != b;
  print "adjacent fp64 literals distinct: ", a != b, "\n";
  print "  ", a, " ", b, "\n";
}

method AdjacentFp32Literals() {
  var a: fp32 := ~0.1;
  var b: fp32 := ~0.10000001;
  assert a != b;
  print "adjacent fp32 literals distinct: ", a != b, "\n";
  print "  ", a, " ", b, "\n";
}

// Exact literals must be unaffected, and the sign of a zero must survive. A decimal literal carries
// no signed zero -- -0.0 is negation applied to 0.0 -- so the sign lives only in the resolver's value.
method ExactLiterals() {
  var half: fp64 := 0.5;
  var two: fp64 := 2.0;
  var negZero: fp64 := -0.0;
  var posZero: fp64 := 0.0;

  assert negZero != posZero;
  assert negZero.IsNegative && negZero.IsZero;
  print "exact literals: ", half, " ", two, "\n";
  print "signed zeros: ", negZero, " ", posZero, " distinct: ", negZero != posZero, "\n";
}

// Literals at the edges of the format, where a shortened decimal is most likely to go wrong.
method ExtremeLiterals() {
  var big: fp64 := ~1.7976931348623157e308;
  var tiny: fp64 := ~1e-300;
  var smallest: fp64 := ~5e-324;

  assert big == fp64.MaxValue;
  assert smallest == fp64.MinSubnormal;
  print "largest fp64 is MaxValue: ", big == fp64.MaxValue, "\n";
  print "5e-324 is MinSubnormal: ", smallest == fp64.MinSubnormal, "\n";
  print "1e-300: ", tiny, "\n";
}

// Printed output is written the way a Dafny literal is written, so it can be read back. These
// literals are exactly what the program above prints for the same constants.
method PrintedOutputReadsBack() {
  var largest: fp64 := ~1.7976931348623157e308;
  var smallest: fp64 := ~5e-324;
  var eps: fp64 := ~2.220446049250313e-16;
  var largest32: fp32 := ~3.4028235e38;
  var smallest32: fp32 := ~1e-45;

  assert largest == fp64.MaxValue;
  assert smallest == fp64.MinSubnormal;
  assert eps == fp64.Epsilon;
  assert largest32 == fp32.MaxValue;
  assert smallest32 == fp32.MinSubnormal;

  print "printed constants read back: ",
        largest == fp64.MaxValue, " ", smallest == fp64.MinSubnormal, " ",
        eps == fp64.Epsilon, " ", largest32 == fp32.MaxValue, " ",
        smallest32 == fp32.MinSubnormal, "\n";
  print "and print as: ", largest, " ", smallest, " ", eps, "\n";
  print "             ", largest32, " ", smallest32, "\n";
}

// A literal where the resolver and a correctly-rounding parser disagree, the pinned Boogie's
// decimal-to-BigFloat conversion rounding twice (boogie-org/boogie#1141 fixes it, unreleased). The
// resolver reads ~1e-5 as the double one ULP below 1e-5, and the compiled constant must be the
// resolver's, that being the value the proof is about.
//
// EXPIRES ON THE NEXT BOOGIE BUMP. Past #1141 the line below prints 1e-5 and this test fails, which
// is the signal that the neighbourhood search in CsharpCodeGenerator.FloatLiteralText is dead and
// should go, along with this method.
method PinnedUntilTheBoogieBump() {
  var offByOne: fp64 := ~1e-5;
  print "~1e-5 resolves to: ", offByOne, "\n";
}

// A real literal converted to a floating-point type is folded to a literal at compile time, while a
// non-literal real goes through the runtime conversion. Both must round once, and at the TARGET
// width: folding through fp64 first would give 1.0 here, one ULP below the correctly rounded fp32,
// and would range-check 1e39 against fp64 and emit an identifier that does not compile.
method FoldedAndUnfoldedAgree() {
  var r: real := 1.000000059604644775390626;
  var folded: fp32 := fp32.FromReal(1.000000059604644775390626);
  var viaRuntime: fp32 := fp32.FromReal(r);
  print "folded == via runtime: ", folded == viaRuntime, "\n";
  print "  both: ", folded, " ", viaRuntime, "\n";

  var big: real := 1e39;
  print "1e39 as fp32 overflows to: ", fp32.FromReal(1e39), " ", fp32.FromReal(big), "\n";
}

method Main() {
  AdjacentFp64Literals();
  AdjacentFp32Literals();
  ExactLiterals();
  ExtremeLiterals();
  PrintedOutputReadsBack();
  PinnedUntilTheBoogieBump();
  FoldedAndUnfoldedAgree();
}
