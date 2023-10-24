// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file ensures that trigger splitting picks the right tokens

ghost function Id(i: int): int { i }

method MSuchThat()
  requires forall x | x > 0 :: Id(x) > 1 && x > 2 && x > -1 { }

method MImplies()
  // The bodies of the two terms that are produced here are both
  // BinaryExpressions(==>); the token they use, however, is that of the RHS
  // terms of these implications; otherwise, error messages would get stacked on
  // the ==> sign
  requires forall x :: x > 0 ==> Id(x) > 1 && x > 2 && x > -1 { }

method M() {
  if * {
    MImplies();
  } else {
    MSuchThat();
  }
}
