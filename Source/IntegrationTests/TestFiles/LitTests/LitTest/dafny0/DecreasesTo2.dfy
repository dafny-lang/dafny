// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Parentheses but missing "to"

method BadParse0() {
  assert (decreases); // parsing error
}

method BadParse1() {
  assert (nonincreases); // parsing error
}

// Arguments and parentheses, but missing "to"

method BadParse2() {
  assert (10 decreases); // parsing error
}

method BadParse3() {
  assert (nonincreases 20); // parsing error
}

method BadParse4() returns (ghost b: bool) {
  b := (Lemma(0); true decreases to Lemma(1); false); // parsing error: needs parens around (Lemma(1); false)
}

lemma Lemma(x: int) {
}
