// RUN: %exits-with 4 %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module ImportByName {
  module A {
    type T(0)
    function method P(): T
    method M(t: T)
  }

  module B {
    import A
  }

  module C {
    import A
    type K = A.T
    import W_A = W_B
    import W_B = A
  }

  module D {
    import B
    import C

    method Client() returns (t: B.A.T, u: C.A.T) {
      t := u;
      u := t;
      var x, y := B.A.P(), C.A.P();
      assert x == y;
      C.A.M(t);
      B.A.M(u);
      var anything;
      assert t == anything;  // error: (testing that it's not possible to prove false here)
    }
  }

  module E {
    import A
    import B
    import C
    method Client() returns (r: A.T, k: C.K) {
      var x, y, z := B.A.P(), C.A.P(), A.P();
      assert x == z == y;
      r, r, r := x, y, z;
      k, k, k, k := x, y, z, r;
      assert r == C.W_A.P();
      assert r == C.W_B.P();
      var anything;
      assert r == anything;  // error: (testing that it's not possible to prove false here)
    }
  }
}

// ------------------------------------------------------------



module ImportOpened {
  module A {
    type T(0)
    function method P(): T
    method M(t: T)
  }

  module B {
    import opened A
    type T = A.T
  }

  module C {
    import opened A
    type K = T
    type L = A.T  // should work when name is qualified, too
    import W_A = W_B
    import W_B = A
  }

  module C' {
    import A  // import by name
    type K = A.T
  }

  module D {
    import opened B
    import opened C
    import opened C'

    method Client() returns (t: B.A.T, u: C.A.T, v: C'.A.T, w: B.T) {
      t, u, v, w := u, v, w, t;
      var x, y, z := B.A.P(), C.A.P(), C'.A.P();
      assert x == y == z;
      var o;
      z, o := C'.A.P(), A.P();
      assert z == o;

      B.A.M(u);
      C.A.M(t);
      C'.A.M(t);
      var anything;
      assert t == anything;  // error: (testing that it's not possible to prove false here)
    }
  }

  module E {
    import opened A
    import opened B
    import opened C
    method Client() returns (r: A.T, k: C.K, l: C.L, m: K, n: L) {
      var x, y, z := B.A.P(), C.A.P(), A.P();
      assert x == z == y;
      r, r, r := x, y, z;
      k, k, k, k := x, y, z, r;
      l, l, l, l, l := x, y, z, r, k;
      m, n := k, l;
      assert m == n == k;
      assert r == C.W_A.P() == C.W_B.P();
      assert r == W_A.P() == W_B.P();
      var anything;
      assert r == anything;  // error: (testing that it's not possible to prove false here)
    }
  }
}

module AmbiguousModuleReference {
  module A {
    module Inner {
      predicate Q()
    }
  }
  module B {
    module Inner {
      predicate Q()
    }
  }
  module Client {
    import A
    import B
    method M() {
      assert A.Inner.Q() <==> B.Inner.Q();  // error: no reason to think these would be equal
    }
  }
}
