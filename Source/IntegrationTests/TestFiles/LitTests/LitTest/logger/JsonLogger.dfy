// The CHECKs pin an ordering, but vcResults is emitted in completion order and the VCs are
// verified in parallel. Verify on one core, as the other order-pinning tests do.
// RUN: %exits-with 4 %baredafny verify --show-snippets:false --log-format:json --isolate-assertions --cores=1 "%s" > "%t"
// Also test old CLI
// RUN: %exits-with 4 %baredafny /compile:0 /verificationLogger:json /vcsSplitOnEveryAssert /vcsCores:1 "%s" >> "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: vcNum.:1,.outcome.:.Valid.*vcNum.:2,.outcome.:.Invalid
// CHECK: vcNum.:1,.outcome.:.Valid.*vcNum.:2,.outcome.:.Invalid
method M(x: int, y: int)
  requires y > 0
  requires x > 0
{
  var d := x / y;
  assert(d * y == x); // Should fail
}
