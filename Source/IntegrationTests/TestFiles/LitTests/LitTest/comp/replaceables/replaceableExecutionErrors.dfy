// RUN: ! %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

replaceable module NeverReplaced {
  method Foo() returns (i: int) 
    ensures i >= 2
}

replaceable module ReplacedThrice {
  method Foo() returns (i: int) 
    ensures i >= 2
}

module Replace1 replaces ReplacedThrice {
  method Foo() returns (i: int) {
    return 3;
  }
}

module Replace2 replaces ReplacedThrice {
  method Foo() returns (i: int) {
    return 3;
  }
}

module Replace3 replaces ReplacedThrice {
  method Foo() returns (i: int) {
    return 3;
  }
}

method Main() {
  var x := NeverReplaced.Foo();
  print x, "\n";
  var y := ReplacedThrice.Foo();
  print y, "\n";
}