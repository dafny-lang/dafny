// RUN: %exits-with 4 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T {
  method M()
  ghost predicate P()
  ghost function F(): int
}

class C extends T {
  method M() // method might modify an object not in the parent trait context's modifies clause
    modifies this

  ghost predicate P() // predicate might read an object not in the parent trait context's reads clause
    reads this

  ghost function F(): int // function might read an object not in the parent trait context's reads clause
    reads this
}
