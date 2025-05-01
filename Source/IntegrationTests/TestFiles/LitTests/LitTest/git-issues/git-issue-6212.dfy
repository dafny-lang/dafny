// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny build %args --no-verify -t:cs "%s" >> "%t"
// RUN: %baredafny build %args --no-verify -t:js "%s" >> "%t"
// RUN: %baredafny build %args --no-verify -t:cpp "%s" >> "%t"
// RUN: %baredafny build %args --no-verify -t:java "%s" >> "%t"
// RUN: %baredafny build %args --no-verify -t:go "%s" >> "%t"
// RUN: %baredafny build %args --no-verify -t:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module Test {
  function FindB(): set<string>
  {
    var elems := ["a", "a", "b"];
    var elemsSet := set id <- elems;
    set x | x in elems && multiset(elems)[x] >= 1
  }
}