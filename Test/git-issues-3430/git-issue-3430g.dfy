// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Checks that too many ^ gives an error

module A {
  module B {
    module C {
      const z := 20;
    }
    module D {
      import X = ^.C
      method m() {
        assert X.z == 20;
      }
    }
    module E {
      import X = ^.^.C
      method m() {
        assert X.z == 10;
      }
    }
    module F {
      module C {
        const z := 30
      }
      import X = C
      method m() {
        assert X.z == 30;
      }
    }
    module G {
      import X = ^.^.^.C
      method m() {
        assert X.z == 40;
      }
    }
  }
  module C {
    const z := 10;
  }
}

module C {
  const z := 40;
}
