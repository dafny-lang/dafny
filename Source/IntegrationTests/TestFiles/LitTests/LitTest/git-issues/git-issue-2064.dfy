// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"

module CoreTests {
  abstract module UnitTestParent {
    type T(!new)
    type U(==)
    type V(0)
    type W(00)
  }

  module OpaqueType refines UnitTestParent {
    type A
    type T = A // error: A is not (!new)
    type U = A // error: A is not (==)
    type V = A // error: A is not (0)
    type W = A // error: A is not (00)
  }

  module OpaqueTypeGood refines UnitTestParent {
    type A(!new)
    type B(==)
    type C(0)
    type D(00)
    type T = A
    type U = B
    type V = C
    type W = D
  }

  module OpaqueTypeMixedUp refines UnitTestParent {
    type A(!new)
    type B(==)
    type C(0)
    type D(00)
    type T = D // error: D is not (!new)
    type U = A // error: A is not (==)
    type V = B // error: B is not (0)
    type W = C // fine, since C is (0), and (0) implies (00)
  }

  module Int refines UnitTestParent {
    type A = int
    type T = A
    type U = A
    type V = A
    type W = A
  }

  module Arrow refines UnitTestParent {
    type A = int -> object
    type T = A // error: A is not (!new)
    type U = A // error: A is not (==)
    type V = A // error: A is not (0)
    type W = A // error: A is not (00)
  }

  module ArrowGood refines UnitTestParent {
    type A = int ~> int
    type T = A
    type U = A // error: A is not (==)
    type V = A
    type W = A
  }

  module ArrowDirect refines UnitTestParent {
    type T = int -> object // error: RHS is not (!new)
    type U = int -> object // error: RHS is not (==)
    type V = int -> object // error: RHS is not (0)
    type W = int -> object // error: RHS is not (00)
  }

  module Class refines UnitTestParent {
    class A { }
    type T = A // error: A is not (!new)
    type U = A
    type V = A // error: A is not (0)
    type W = A // error: A is not (00)
  }

  module ClassDirect refines UnitTestParent {
    class T { } // error: T is not (!new)
    class U { }
    class V { } // error: T is not (0)
    class W { } // error: T is not (00)
  }

  module NullableClass refines UnitTestParent {
    class A { }
    type T = A? // error: A? is not (!new)
    type U = A?
    type V = A?
    type W = A?
  }

  module InstantiatedDatatypeBad0 refines UnitTestParent {
    datatype Record<X> = Record(X)
    type A = Record<object>
    type T = A // error: A is not (!new)
    type U = A
    type V = A // error: A is not (0)
    type W = A // error: A is not (00)
  }

  module InstantiatedDatatypeBad1 refines UnitTestParent {
    datatype Record<X> = Record(X, ghost X)
    type A = Record<int>
    type T = A
    type U = A // error: A is not (==)
    type V = A
    type W = A
  }

  module InstantiatedDatatypeGood refines UnitTestParent {
    datatype Record<X> = Record(X)
    type A = Record<set<real>>
    type T = A
    type U = A
    type V = A
    type W = A
  }
}

module BugReport0 {
  abstract module Parent {
    type T(!new, ==)

    twostate lemma L(new t: T)
      ensures old(allocated(t))
    {}
  }

  module Child refines Parent {
    // Once, the following line did not result in any complaints
    class T { // error: T does not support (!new)
      var a: int
      constructor(a: int) ensures this.a == a { this.a := a; }
    }

    method boom() {
      var c := new T(0);
      assert !old(allocated(c));
      L(c);
      assert old(allocated(c));
      assert false;
    }
  }
}

module BugReport1 {
  abstract module Parent {
    type U(00)

    lemma Mk() returns (u: U) {
      u :| true;
    }
  }

  module Child refines Parent {
    type False = x: int | false witness *

    datatype U = U(f: False) // error: does not support (00)
  }

  method Main() ensures false {
    ghost var u: Child.U := Child.Mk();
    ghost var f: Child.False := u.f;
  }
}

module BugReport2 {
  abstract module Parent {
    type U(00)

    lemma Mk() returns (u: U) {
      u :| true;
    }
  }

  module Child refines Parent {
    type False = x: int | false witness *

    // Once, the following line was accepted without any complaints
    class U { // error: U does not support (00)
      var f: False
      constructor(f: False) { this.f := f; }
    }
  }

  method Main() ensures false {
    ghost var u: Child.U := Child.Mk();
    ghost var f: Child.False := u.f;
  }
}

module BugReport2' {
  abstract module Parent {
    type U(0)

    lemma Mk() returns (u: U) {
      u :| true;
    }
  }

  module Child refines Parent {
    type False = x: int | false witness *

    class U { // error: U does not support (0)
      var f: False
      constructor(f: False) { this.f := f; }
    }
  }

  method Main() ensures false {
    ghost var u: Child.U := Child.Mk();
    ghost var f: Child.False := u.f;
  }
}
