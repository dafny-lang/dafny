// RUN: %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  module F {
    import opened _.A.B
    method m() {
      assert c == 20;
    }
  }    
  module B {
    const c := 20
    module C {
      const c := 10
    }
  }
  module D {
    import opened ^.^.B.C
    method m() {
      assert c == 10;
    }
  }
  module E {
    import opened ^.^.B
    method m() {
      assert c == 20;
    }
  }
}

