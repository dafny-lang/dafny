// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

// A compiled literal has to be the same value the verifier reasoned about. It is easy for it not
// to be: the verifier holds the exact rounded value, while the generated code holds whatever
// decimal the compiler chose to write, and a decimal that is one digit short names the
// neighbouring float. BigFloat.ToDecimalString has exactly that defect -- for the fp64 nearest to
// 4/7 it prints 0.5714285714285713 -- so literals are emitted as bit patterns instead.
//
// The pairs below are adjacent floats whose shortest decimals differ only in the last digit. If a
// literal were ever rounded or shortened on the way to the generated code, the two members of a
// pair would collapse onto one value, and the assert and the print would disagree.

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

// Exact literals must be unaffected, and the sign of a zero has to survive. A decimal literal
// carries no signed zero -- -0.0 is negation applied to the literal 0.0 -- so the sign exists only
// in the value the resolver computed.
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

// A literal where the resolver and a correctly-rounding parser disagree, because the pinned
// Boogie's decimal-to-BigFloat conversion rounds twice (boogie-org/boogie#1141 fixes it but is not
// in a release). The resolver reads ~1e-5 as the double one ULP below 1e-5, and the compiled
// constant has to be the resolver's, because that is the value the proof is about.
//
// THIS TEST IS A REMINDER WITH AN EXPIRY DATE. When Boogie is bumped past #1141 the line below will
// print 1e-5 and this test will fail. That failure is the signal that the neighbourhood search in
// CsharpCodeGenerator.FloatLiteralText is now dead code and should be deleted, along with this
// method. Until then, the search is what keeps the compiled constant equal to the verified one.
method PinnedUntilTheBoogieBump() {
  var offByOne: fp64 := ~1e-5;
  print "~1e-5 resolves to: ", offByOne, "\n";
}

method Main() {
  AdjacentFp64Literals();
  AdjacentFp32Literals();
  ExactLiterals();
  ExtremeLiterals();
  PrintedOutputReadsBack();
  PinnedUntilTheBoogieBump();
}
