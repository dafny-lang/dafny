// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  datatype M = C // note, top-level declaration has same name as enclosing module
  datatype SomethingElse = SE
}

module N {
  datatype M = D
  datatype Record = R
}

module O {
  datatype M = E
}

module ClientOfMNO {
  import opened N
  import opened M
  import opened O

  method Bar0(m: M) // this M refers to the type inside module M
  {
    assert m == C;
  }

  method Bar1(m: N.M)
  {
    assert m == D;
  }

  method Bar2(m: O.M)
  {
    assert m == E;
  }
}

module ClientOfNOAndRenamedM {
  import opened N
  import opened RenamedM = M
  import opened O

  method Bar0(m: RenamedM.M)
  {
    assert m == C;
  }

  method Bar1(m: N.M)
  {
    assert m == D;
  }

  method Bar2(m: O.M)
  {
    assert m == E;
  }

  method Bar3(m: M) // error: M is ambiguous (N, RenamedM, O)
  {
  }
}

module ClientOfJustNO {
  import opened N
  import opened O

  method Bar0(m: M) // error: M is ambiguous (N.M or O.M)
  {
  }

  method Bar1(m: N.M)
  {
    assert m == D;
  }

  method Bar2(m: O.M)
  {
    assert m == E;
  }
}

module ClientOfJustM {
  import opened M

  method Bar0() {
    var c0 := C;
    var c1 := M.C;
    var c2 := M.M.C; // error: the first M refers to the type, not the module
  }

  method Bar1() {
    var c0 := SE;
    var c1 := SomethingElse.SE;
    var c2 := M.SomethingElse.SE; // error: the first M refers to the type, not the module
  }
}

module ClientOfJustM' {
  import opened M = M // explicitly name M M (but this is no different from just "import opened M")

  method Bar0() {
    var c0 := C;
    var c1 := M.C;
    var c2 := M.M.C; // error: the first M refers to the type, not the module
  }

  method Bar1() {
    var c0 := SE;
    var c1 := SomethingElse.SE;
    var c2 := M.SomethingElse.SE; // error: the first M refers to the type, not the module
  }
}

module ClientOfJustMRenamed {
  import opened MRenamed = M

  method Bar0() {
    var c0 := C;
    var c1 := M.C;
    var c2 := MRenamed.M.C;
  }

  method Bar1() {
    var c0 := SE;
    var c1 := SomethingElse.SE;
    var c2 := MRenamed.SomethingElse.SE;
  }
}

module ClientOfJustN {
  import opened N

  method Bar() {
    var c0 := R;
    var c1 := Record.R;
    var c2 := N.Record.R;
  }
}

module ClientOfJustN' {
  import opened N = N // explicitly name N N

  method Bar() {
    var c0 := R;
    var c1 := Record.R;
    var c2 := N.Record.R;
  }
}

module ClientOfJustNRenamed {
  import opened NRenamed = N

  method Bar() {
    var c0 := R;
    var c1 := Record.R;
    var c2 := NRenamed.Record.R;
  }
}

module NothingOpened {
  import N
  import M
  import O

  method Bar0(m: M.M)
  {
    assert m == M.C == M.M.C; // note, the M in M.C and the first M in M.M.C refer to the module
  }

  method Bar1(m: N.M)
  {
    assert m == N.D == N.M.D;
  }

  method Bar2(m: O.M)
  {
    assert m == O.E == O.M.E;
  }
}

module RenamedModuleDoesNotFollowException {
  import opened Record = N

  method Bar0(m: M) {
  }

  method Bar1(r: Record) { // error: Record is the local name for the (opened-)imported module
  }

  method Bar2(r: Record.Record) {
    assert r == R;
    assert r == Record.R; // Record refers to the module
    assert r == Record.Record.R; // the first Record refers to the module
  }
}

module Q {
  datatype Q = Q
}

module QClient {
  import opened Q

  method Bar(q: Q) { // Q refers to the type
    var r := Q; // this Q refers to the constructor
    assert q == r;
  }
}

module W {
  datatype A = W
  datatype W = A
}

module WClient {
  import opened W

  method Bar(a: A, w: W) { // A and W are the types
    var a' := W; // W is the constructor
    var w' := A; // A is the constructor
    assert a == a';
    assert w == w';
  }
}

module U {
  datatype X = Ctor
}
module V {
  datatype Y = Ctor
}
module Ctor {
  datatype Ctor = Abc
}
module UVClient {
  import opened U
  import opened Ctor
  import opened V

  method Bar0(x: X, y: Y, c: Ctor) {
    var d := Ctor; // error: ambiguous constructor
  }

  method Bar1() {
    var dx := X.Ctor;
    dx := U.X.Ctor;
    dx := U.Ctor;
    var dy := Y.Ctor;
    dy := V.Y.Ctor;
    dy := V.Ctor;
    var e := Ctor.Abc; // this Ctor refers to the module
  }
}

module Option {
  datatype Option<T> = Some(x: T) | None
}

module ClientOfOption {
  import opened Option

  function Foo(o: Option<int>): int {
    match o
    case Some(x) => x
    case None => 0
  }
}

module NoAmbiguity {
  module Option {
    datatype Option = O {
      static const a: int := 1
    }
  }

  module OtherModuleDefiningOption {
    datatype Option = O {
      static const a: int := 1
    }
  }

  module Client {
    import opened Option
    import opened OtherModuleDefiningOption

    method M() {
      print Option.a;
      // Not an error: in previous versions of Dafny, this did not resolve at
      // all, because `Option` referred to the module `Option`.
    }
  }
}

module AmbiguityFromConstructor {
  module Option {
    datatype Foo = a
    datatype Option = O {
      static const a := 1
    }
  }

  module Client {
    import opened Option
    method M() {
      print Option.O;
      // No error: `Some` is accessible through the module and through the
      // datatype but refers to the same entity in both.

      print Option.a;
      // Error: `a` used to refer to the constructor of `Foo` and now would
      // refer to `Option.Option.a`.
    }
  }
}

module OtherAmbiguityFromDependencyOnDeclarationOrdering {
  module A {
    datatype A = XYZ
    datatype Foo = XYZ
  }

  module B {
    datatype Foo = XYZ
    datatype B = XYZ
  }

  module Client {
    import opened A
    import opened B

    method M() {
      print A.XYZ;
      // No error: `XYZ` is accessible through the module and through the
      // datatype and is ambiguous in the module.

      print B.XYZ;
      // No error: `XYZ` is accessible through the module and through the
      // datatype and is ambiguous in the module.
    }
  }
}

module AmbiguityFromMember {
  module Option {
    type a = int
    datatype Option = O {
      static const a := 1
    }
  }

  module Client {
    import opened Option
    method M() {
      print Option.a;
      // Error: `a` used to refer to `type a` and now would
      // refer to `const a := 1`
    }
  }
}

module AmbiguityFromStaticMember {
  module Option {
    const a := 2
    datatype Option = O {
      static const a := 1
    }
  }

  module Client {
    import opened Option
    method M() {
      print Option.a;
      // Error: `a` used to refer to `const a := 2` and now would
      // refer to `const a := 1`
    }
  }
}

module AmbiguityWithRecords {
  module Record {
    const a := 2
    datatype Record = Record {
      static const a := 1
    }
  }

  module Client {
    import opened Record
    method M() {
      print Record.Record;
      // Error: `Record.Record` could mean the datatype or the constructor.  This
      // message could be silenced with a bit more work, if a user requests it.
    }
  }
}

module NoAmbiguityFromRename {
  module Option {
    const a := 2
    datatype Option = O {
      static const a := 1
    }
  }

  module Client {
    import opened Opt = Option
    method M() {
      print Option.a;
      // No error: `Option` is unambiguous
    }
  }
}
