// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


// It would be great if Dafny was able to verify the following statements;
// otherwise, trigger splitting prevents `exists b :: b || not b` from verifying

method M() {
  assert exists b : bool {:nowarn} :: b; // WISH
  assert exists b : bool {:nowarn} :: !b; // WISH
}
