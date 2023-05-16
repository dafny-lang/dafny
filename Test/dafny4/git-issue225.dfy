// RUN: %exits-with 2 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module SiblingImport {
  abstract module AbstractModule {
    method Print() { print "hello\n"; }
  }
  module SiblingModule {
    import AbstractModule  // error: cannot import abstract module into a non-abstract module
    method Test() {
      AbstractModule.Print();
    }
  }
}

module OpenedImport {
  abstract module AbstractModule {
    method Print() { print "hello\n"; }
  }
  module SiblingModule {
    import opened AbstractModule  // error: cannot import abstract module into a non-abstract module
    method Test() {
      Print();
    }
  }
}

module ImportAlias {
  abstract module AbstractModule {
    method Print() { print "hello\n"; }
  }
  import Alias = AbstractModule  // error: cannot import abstract module into a non-abstract module
  method Test() {
    Alias.Print();
  }
}

module QualifiedImport {
  module M {
    abstract module AbstractModule {
      method Print() { print "hello\n"; }
    }
  }
  import Alias = M.AbstractModule  // error: cannot import abstract module into a non-abstract module
  method Test() {
    Alias.Print();
  }
}

module TwoAlias {
  module M {
    abstract module AbstractModule {
      method Print() { print "hello\n"; }
    }
    abstract module AnotherAbstractModule {
      import A = AbstractModule
    }
  }
  import Alias = M.AnotherAbstractModule.A  // error: cannot import abstract module into a non-abstract module
  method Test() {
    Alias.Print();
  }
}

module CompiledInsideAbstract {
  abstract module AbstractModule {
    module NonAbstractModule {
      method Print() { print "hello\n"; }
    }
  }
  method Test() {
    AbstractModule.NonAbstractModule.Print();  // error: cannot use abstract module (AbstractModule) in a non-abstract module
  }
}

module DirectUse {
  abstract module AbstractModule {
    method Print() { print "hello\n"; }
    lemma Lemma()
    datatype Record = Record(x: int)
    function F(): int
    ghost function G(): int
    const c: int
    ghost const d: int
  }
  method Test() {
    AbstractModule.Print();  // error: cannot use abstract module in a non-abstract module
    AbstractModule.Lemma();  // error: cannot use abstract module in a non-abstract module
    var r: AbstractModule.Record;  // error: cannot use abstract module in a non-abstract module
    var f := AbstractModule.F();  // error: cannot use abstract module in a non-abstract module
    ghost var g := AbstractModule.G();  // error: cannot use abstract module in a non-abstract module
    var c := AbstractModule.c;  // error: cannot use abstract module in a non-abstract module
    ghost var d := AbstractModule.d;  // error: cannot use abstract module in a non-abstract module
  }
}

module ProperUse {
  abstract module AbstractModule {
    method Print() { print "hello\n"; }
  }
  module ConcreteModule refines AbstractModule {
    method Print() { print "hello\n"; }
  }
  method Test() {
    ConcreteModule.Print();  // fine
  }
}
