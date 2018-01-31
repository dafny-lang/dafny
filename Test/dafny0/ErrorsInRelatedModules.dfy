// RUN: %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
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
  
  module ClientModule {
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
