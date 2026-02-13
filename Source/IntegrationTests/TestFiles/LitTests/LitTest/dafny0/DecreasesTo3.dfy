// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s" -- --show-proof-obligation-expressions


method M1() {
  assert (1 decreases to 0) && (0 decreases to 1); // error: second conjunct doesn't hold
}

method M2() {
  assert 0 decreases to 1; // error
}

method PrettyPrinting0(b: bool) {
  assert b <==> (0, 1, 2 decreases to (0 nonincreases to 0), b <==> b, 6) <==> b; // error
}

method PrettyPrinting1(b: bool) {
  assert b <==> (3 decreases to 2) <==> !b; // error
}

method PrettyPrinting2(b: bool) {
  assert b <==> b decreases to var two := 2; two <= two; // error
}

lemma Lemma() {
}

method PrettyPrinting3(b: bool) {
  assert (Lemma(); b) <==> (Lemma(); !b) decreases to (Lemma(); false); // error
}

method PrettyPrinting4(b: bool) {
  assert (b decreases to (Lemma(); true), (Lemma(); true)); // error
}
