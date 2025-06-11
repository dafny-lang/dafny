// RUN: %tobinary %s --delete-sources > %t.deleteSources.dbin
// RUN: %resolve --input-format Binary --allow-warnings --stdin < %t.deleteSources.dbin > %t
// RUN: %diff "%s.expect" "%t"

method Foo() {
  assert false; // error
}

method Bar() {
  assert false; // error
}

function F(): int {
  3
} by method {
  assert false; // error
  return 1 + 2;
}

opaque predicate P() { true }

lemma ProveP() ensures P() {
  reveal P();
}

greatest predicate G(x: int) { x == 0 || G(x-2) }

greatest lemma GL(x: int)
  ensures G(x)
{
  GL(x-2) by { ProveP(); }
  assert P(); // should fail
}

class C {
  var more: C?
  constructor ()
    ensures more == null || fresh(more)
}

iterator Iter(c: C?, d: C?)
  modifies c.more // error: c may be null (reported twice)
  reads d.more // error: c may be null (reported twice)
{
}