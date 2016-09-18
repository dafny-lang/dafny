// RUN: %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class A {
  var f: int
  var g: A
}

twostate lemma L8(a: A, new b: A)
  requires a != null
  requires unchanged(a.g)
  modifies a.g  // lemmas are not allowed to have modifies clauses
  decreases old(a.f)
{}
