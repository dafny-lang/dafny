// RUN: %dafny /compile:0 /verificationLogger:text /vcsSplitOnEveryAssert "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: Outcome: Valid
// CHECK: TextLogger.dfy\(11,14\): divisor is always non-zero
// CHECK: Outcome: Invalid
// CHECK: TextLogger.dfy\(12,9\): assertion always holds
method M(x: int, y: int)
  requires y > 0
  requires x > 0
{
  var d := x / y;
  assert(d * y == x); // Should fail
}
