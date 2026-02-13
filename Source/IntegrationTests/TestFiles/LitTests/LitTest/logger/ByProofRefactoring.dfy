// RUN: %baredafny verify --use-basename-for-filename --show-snippets false --show-hints --isolate-assertions --suggest-proof-refactoring --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

opaque predicate P() { true }

method M() requires P() { }

method N() ensures P() { reveal P(); }

method NoSuggestion()
{
  N();
  M();
}

method Call()
{
  assert P() by { reveal P(); }
  M();
}

method CallFixed()
{
  M() by {
    assert P() by { reveal P(); }
  }
}

method Assert()
{
  assert P() by { reveal P(); }
  assert P();
}

method AssertFixed()
{
  assert P() by {
    assert P() by { reveal P(); }
  }
}

method Requires()
  requires P()
{
  assert P();
}

method RequiresFixed()
  requires p: P()
{
  assert P() by {
    reveal p;
  }
}

method CantMove(){
  var b := P();
  assert b by { reveal P(); }
  b := !b;
  assert !b;
}
