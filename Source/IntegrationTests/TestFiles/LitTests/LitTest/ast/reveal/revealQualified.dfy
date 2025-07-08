// RUN: %resolve --type-system-refresh --allow-axioms %s > %t
// RUN: %diff "%s.expect" "%t"

module Prod {
  class Foo {
    function P(x: int): bool {
      true
    }

    static function Q(x: int): bool {
      true
    }
  }

  method StaticRevealWorks() {
    hide *;
      
    reveal Foo.P;
    reveal Foo.Q;
  }

  method InstanceRevealWorks(foo: Foo) {
    hide *;
      
    reveal foo.P;
    reveal foo.Q;
  }
}

module Cons {
  import Prod

  method StaticRevealWorks() {
    hide *;
      
    reveal Prod.Foo.P;
    reveal Prod.Foo.Q;
  }
}
