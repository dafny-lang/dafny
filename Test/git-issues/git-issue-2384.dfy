// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T {
  method M()
  predicate P()
  function F(): int
}

class C extends T {
  method M() // method might modify an object not in the parent trait context's modifies clause
    modifies this

  predicate P() // predicate might read an object not in the parent trait context's reads clause
    reads this

  function F(): int // function might read an object not in the parent trait context's reads clause
    reads this
}
