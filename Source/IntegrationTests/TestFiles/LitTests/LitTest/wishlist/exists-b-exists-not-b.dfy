// RUN: %testDafnyForEachResolver "%s"


// Z3 4.16.0 can now verify these statements (previously a wishlist item).
// Trigger splitting no longer prevents `exists b :: b || not b` from verifying.

method M() {
  assert exists b : bool {:nowarn} :: b;
  assert exists b : bool {:nowarn} :: !b;
}
