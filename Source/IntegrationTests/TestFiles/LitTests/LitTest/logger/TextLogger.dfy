// RUN: %exits-with 4 %baredafny verify --show-snippets:false --log-format:text --isolate-assertions "%s" > "%t"
// RUN: %exits-with 4 %baredafny /compile:0 /verificationLogger:text /vcsSplitOnEveryAssert "%s" >> "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: Overall outcome: Errors
// CHECK: Overall time: .*
// CHECK: Overall resource count: .*
// CHECK: Maximum assertion batch time: .*
// CHECK: Maximum assertion batch resource count: .*
// CHECK: Outcome: Valid
// CHECK: Duration: .*
// CHECK: Resource count: .*
// CHECK: TextLogger.dfy\(34,14\): divisor is always non-zero
// CHECK: Outcome: Invalid
// CHECK: Duration: .*
// CHECK: Resource count: .*
// CHECK: TextLogger.dfy\(35,3\): assertion always holds
// CHECK: Overall outcome: Errors
// CHECK: Overall time: .*
// CHECK: Overall resource count: .*
// CHECK: Maximum assertion batch time: .*
// CHECK: Maximum assertion batch resource count: .*
// CHECK: Outcome: Valid
// CHECK: Duration: .*
// CHECK: Resource count: .*
// CHECK: TextLogger.dfy\(34,14\): divisor is always non-zero
// CHECK: Outcome: Invalid
// CHECK: Duration: .*
// CHECK: Resource count: .*
// CHECK: TextLogger.dfy\(35,3\): assertion always holds
method M(x: int, y: int)
  requires y > 0
  requires x > 0
{
  var d := x / y;
  assert(d * y == x); // Should fail
}
