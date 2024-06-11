// RUN: %exits-with 4 %baredafny verify --log-format:text --boogie -trackVerificationCoverage "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-NOT:     Proof dependencies:
// CHECK-NOT:     Unused by proof:

lemma NotTrue(x: int)
  requires x > 0
  ensures x + 1 < 0
{}
