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
  }
  module C {
    const z := 10;
  }
}
