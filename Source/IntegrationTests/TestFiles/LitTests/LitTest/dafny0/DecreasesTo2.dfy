// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method BadParse1() {
  assert (1 decreases to);
}

method BadParse3() {
  assert (1 decreases);
}

method BadParse2() {
  assert (decreases to);
}

