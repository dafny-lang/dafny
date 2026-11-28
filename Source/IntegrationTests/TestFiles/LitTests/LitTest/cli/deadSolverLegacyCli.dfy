// A dead solver fails verification without crashing /xml or the text logger.
// One check only: with more checks than /vcsCores, a dead solver can hang Boogie 3.5.5.
// RUN: %exits-with 4 %dafny /compile:0 /proverOpt:PROVER_PATH=/usr/bin/false /xml:"%t.xml" /verificationLogger:text "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: Dafny program verifier finished with 0 verified, 0 errors, 1 solver exceptions
// CHECK: Overall outcome: SolverException
// UNSUPPORTED: windows

method M() {
  assert 1 + 1 == 2;
}
