// RUN: %exits-with 4 %baredafny verify --show-snippets:false --log-format:text "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: Overall outcome: Errors
// CHECK: Overall time: .*
// CHECK: Overall resource count: .*
// CHECK: Maximum assertion batch time: .*
// CHECK: Maximum assertion batch resource count: .*
// CHECK: Outcome: Invalid
// CHECK: Duration: .*
// CHECK: Resource count: .*
// CHECK: TextLoggerBatch.dfy\(17,14\): divisor is always non-zero
// CHECK: TextLoggerBatch.dfy\(18,3\): assertion always holds
method M(x: int, y: int)
  requires y > 0
  requires x > 0
{
  var d := x / y;
  assert(d * y == x); // Should fail
}
