// RUN: %exits-with 2 %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file gives some regression tests, where Dafny once had crashed when an imported module
// or nested module was not successfully resolved.

module ImportTests {
  module LibraryModule {
    datatype Packet = Packet(UndeclaredType)  // error: UndeclaredType
  }

  module MainModule {
    import LibraryModule
    method M() {
      var x: set<LibraryModule.Packet>;  // this once caused crash
    }
  }
}

module NestedTests {
  module OuterModule {
    module NestedModule {
      datatype Packet = Packet(UndeclaredType)  // error: UndeclaredType
    }

    method M() {
      var x: set<NestedModule.Packet>;  // this once caused crash
    }
  }
}

module FacadeTests {
  module Template {
    datatype Packet = Packet(UndeclaredType)  // error: UndeclaredType
  }

  abstract module ClientModule {
    import T : Template
    method M() {
      var x: set<T.Packet>;  // this once caused crash
    }
  }
}

module GoodDoublyNestedModule {
  module Middle {
    module Inner {
      class GoodType { }
    }
  }
  import MI = Middle.Inner
}

module BadImportNames {
  module Middle {
    module Inner {
    }
  }
  import MI = Middle.I  // error: there's no module called Middle.I
}

// --------------------------------------------------------------------------------

module ModuleWithErrors {
  datatype Packet = Packet(UndeclaredType)  // error: UndeclaredType
}

module ClientOfErroneousModule0 {
  import ModuleWithErrors // error: not resolving this module, because of error in imported module
  method M() {
    var u: int := true; // no error is reported here
  }
}

module ClientOfErroneousModule1 {
  import ModuleWithErrors // no additional error reported here, because this module proper is empty
}

module ClientOfErroneousModule2 {
  import ModuleWithErrors // error: not resolving this module, because of error in imported module
  class C {
    method M() {
      var u: int := true; // no error is reported here
    }
  }
}

module ClientOfErroneousModule2' {
  import ModuleWithErrors // no additional error reported here, because this module proper is empty
  trait T { }
  class C { }
}

module ClientOfErroneousModule2'' {
  import ModuleWithErrors // error: not resolving this module, because of error in imported module
  trait T { }
  class C extends T { }
}

module ClientOfErroneousModule2'3 {
  import ModuleWithErrors // error: not resolving this module, because of error in imported module
  class C extends TraitThatDoesNotExist { }
}

module ClientOfErroneousModule3 {
  import ModuleWithErrors // error: not resolving this module, because of error in imported module
  datatype Color = Artic | Mint | Lilac
  {
    method M() {
      var u: int := true; // no error is reported here
    }
  }
}

module ClientOfErroneousModule3' {
  import ModuleWithErrors // no additional error reported here, because this module proper is empty
  datatype Color = Artic | Mint | Lilac
}

module ClientOfErroneousModule3'' {
  import ModuleWithErrors // error: not resolving this module, because of error in imported module
  datatype Color = Artic | Mint(u: TypeDoesNotExist) | Lilac // no error reported here
}

module ClientOfErroneousModule4 {
  import ModuleWithErrors // no additional error reported here, because this module proper is empty
  module InnerModule {
    method M() {
      var u: int := true; // error: cannot assign bool to int
    }
  }
}

module ClientOfErroneousModule5 {
  import ModuleWithErrors // error: not resolving this module, because of error in imported module
  module InnerModule {
    method M() {
      var u: int := true; // error: cannot assign bool to int
    }
  }
  newtype MyInt = int {
    method M() {
      var u: int := true; // no error is reported here
    }
  }
}

module ClientOfErroneousModule6 {
  import ModuleWithErrors
  trait EverythingHasTheSameName<X> { }
  class EverythingHasTheSameName<X> { } // error: duplicate name
  datatype EverythingHasTheSameName<X> = Y // error: duplicate name
}

module ClientOfErroneousModule7 {
  import ModuleWithErrors // error: not resolving this module, because of error in imported module
  trait A<X, X> { } // no error reported here
  class B<Y, Y> { } // no error reported here
  datatype C<Z, Z> = R // no error reported here
}

