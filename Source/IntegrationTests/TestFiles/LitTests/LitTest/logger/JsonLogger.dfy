// The CHECK directives below assert an *ordering* of vcResults, but the logger emits them in VC
// completion order, and with assertions isolated the VCs are verified in parallel. Verify with a
// single core so that order is deterministic, as every other test that pins per-VC or per-assertion
// output already does (see verification/progress.dfy and verification/proofDivision/*).
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
