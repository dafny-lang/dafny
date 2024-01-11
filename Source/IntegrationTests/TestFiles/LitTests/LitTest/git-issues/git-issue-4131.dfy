// RUN: %dafny /compile:0 /typeSystemRefresh:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Element { }

class Foo {
  function Collect(M: set<Element>): bool
    reads this, set a | a in M
    // The legacy resolver inferred "a" in the following line to have type "Foo",
    // which results in a type error. This has been fixed in the new resolver.
    decreases (set a | a in M) + {this}
  {
    true
  }
}
