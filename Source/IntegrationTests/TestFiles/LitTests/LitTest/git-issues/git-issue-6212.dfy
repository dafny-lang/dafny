// NONUNIFORM: Testing that we don't need --emit-uncompilable-code.
// RUN: %baredafny build -t:rs %args  --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Test {
  function FindB(): set<string>
  {
    var elems := ["a", "a", "b"];
    var elemsSet := set id <- elems;
    set x | x in elems && multiset(elems)[x] >= 1
  }
}