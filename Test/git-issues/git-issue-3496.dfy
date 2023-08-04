// RUN: %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method m() {
  assume true;
}

method p() {
  assume {:axiom} true;
}
