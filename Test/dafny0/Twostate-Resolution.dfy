// RUN: %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M0 {
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
}

module M1 {
  class C { }
  
  method M(c: C)
    requires unchanged(c)  // error: 'unchanged' not allowed here
    ensures unchanged(c)
  lemma L(c: C)
    requires unchanged(c)  // error: 'unchanged' not allowed here
    ensures unchanged(c)  // error: 'unchanged' not allowed here
  function F(c: C): bool
    requires unchanged(c)  // error: 'unchanged' not allowed here
    ensures unchanged(c)  // error: 'unchanged' not allowed here
  twostate lemma L2(c: C)
    requires unchanged(c)
    ensures unchanged(c)
}
