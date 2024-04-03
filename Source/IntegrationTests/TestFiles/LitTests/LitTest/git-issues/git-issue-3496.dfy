// RUN: %resolve --allow-axioms:false --allow-warnings "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method m() {
  assume true;
}

method p() {
  assume {:axiom} true;
}
