// RUN: ! %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

placeholder module NeverReplaced {
  method Foo() returns (i: int) 
    ensures i >= 2
}

placeholder module ReplacedTwice {
  method Foo() returns (i: int) 
    ensures i >= 2
}

module Replace1 replaces ReplacedTwice {
  method Foo() returns (i: int) {
    return 3;
  }
}

module Replace2 replaces ReplacedTwice {
  method Foo() returns (i: int) {
    return 3;
  }
}

method Main() {
  var x := NeverReplaced.Foo();
  print x, "\n";
  var y := ReplacedTwice.Foo();
  print y, "\n";
}