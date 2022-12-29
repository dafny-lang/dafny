// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// It would be great if Dafny was able to verify the following statements;
// otherwise, trigger splitting prevents `exists b :: b || not b` from verifying

method M() {
  assert exists b : bool {:nowarn} :: b; // WISH
  assert exists b : bool {:nowarn} :: !b; // WISH
}
