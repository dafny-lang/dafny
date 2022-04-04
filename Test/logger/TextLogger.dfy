// RUN: %dafny /compile:0 /verificationLogger:text /vcsSplitOnEveryAssert "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: Overall outcome: Errors
// CHECK: Overall time: .*
// CHECK: Overall resource count: .*
// CHECK: Outcome: Valid
// CHECK: Duration: .*
// CHECK: Resource count: .*
// CHECK: TextLogger.dfy\(18,14\): divisor is always non-zero
// CHECK: Outcome: Invalid
// CHECK: Duration: .*
// CHECK: Resource count: .*
// CHECK: TextLogger.dfy\(19,9\): assertion always holds
method M(x: int, y: int)
  requires y > 0
  requires x > 0
{
  var d := x / y;
  assert(d * y == x); // Should fail
}
