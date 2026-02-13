// RUN: ! %verify --type-system-refresh --bprint=%t.bpl --allow-axioms --isolate-assertions %s > %t
// RUN: %diff "%s.expect" "%t"

const someConst: nat := 10

method Constant() {
  hide *;

  assert someConst >= 0; // pass because of nat type
  assert someConst > 8; // error, hidden
  reveal someConst;
  assert someConst > 9; // success
}