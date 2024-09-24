// RUN: ! %verify --type-system-refresh --isolate-assertions %s > %t
// RUN: %diff "%s.expect" "%t"

predicate P() { true }

method NeedsP()
  requires P()
{}

method M()
  ensures P()
{
  hide P;
  NeedsP() by { reveal P(); }
  assert P(); // should fail
}