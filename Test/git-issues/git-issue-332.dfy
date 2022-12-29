// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var foo := new B.Foo(15);
  print foo.I(), "\n";
}

abstract module A {
  class Foo {
    var x: int
    constructor (u: int) { x := u; }
    twostate function F(): int reads this
    twostate predicate G() reads this
    function H(): int reads this
    function method I(): int reads this
    predicate J() reads this
  }
}

module B refines A {
  class Foo ... {
    twostate function F(): int { old(x) + x }
    twostate predicate G() { old(x) <= x }
    function H(): int { x + 4 }
    function method I(): int { x + 5 }
    predicate J() { x <= x }
  }
}
