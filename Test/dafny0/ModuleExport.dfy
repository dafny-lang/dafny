// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
	export A reveals f provides h
	export E1 provides f reveals g
	export E2 extends A, E1 reveals T
  export Friend extends A reveals g, T provides T.l
	export Fruit reveals Data

  method h() {}
  function f(): int { 818 }
  function g() : int { 819 }
	function k() : int { 820 }

	class T
	{
	  static method l() {}
	}

	datatype Data = Lemon | Kiwi(int)

}

module B {
  import X = A
	method m() {
	  X.h();  // OK
	  assert X.f() == 818; // OK
		assert X.g() == 819; // error
		assert X.k() == 820; // error
		X.T.l(); // error
	}
}

module C {
  import X = A`Friend
	method m() {
	  X.h();  // OK
	  assert X.f() == 818; // OK
		assert X.g() == 819; // OK
		assert X.k() == 820; // error
		X.T.l(); // OK
	}
}

module D {
  import opened A
	method m() {
	  h();  // OK
	  assert f() == 818; // OK
		assert g() == 819; // error
		assert k() == 820; // error
	 }
}

module E {
  import opened A`Fruit

  function G(d: Data): int
    requires d != Data.Lemon
  {
    match d
    case Lemon => G(d)
    case Kiwi(x) => 7
		case Orang => 8  // error
  }
}

module F {
  export F reveals f provides h
	export E1 reveals f, g
	export E2 extends Public2, E1 reveals T		// error: Public2 is not a exported view of F
  export Friend extends F reveals g2, T  // error: g2 is not a member of F
	export Fruit provides Data

  method h() {}
  function f(): int { 818 }
  function g() : int { 819 }
	function k() : int { 820 }

	class T
	{
	  static method l() {}
	}

	datatype Data = Lemon | Kiwi(int)
}

module G {
  export Public reveals f provides h

	method h() {}
  function f(): int { 818 }
  function g() : int { 819 }
	function k() : int { 820 }
}

module H {
  import G  // error: G has no default export
}

module I {
  import G`Public  // OK
}

module J {
  module X {
    // revealing a class provides the types C and C? and also provides the info about whether or not the class has a constructor
    export reveals C, D
    class C {
      constructor Init() { }
    }
    class D {
    }
  }
  module Client {
    import X
    method M(c: X.C, c0: X.C?, d: X.D, d0: X.D?) {  // all of these types are known
      if c0 == null || d0 == null {  // fine to compare c0 and d0 with null
      }
    }
    method P() {
      var c: X.C;
      c := new X.C;  // error: must call a constructor
      c := new X.C.Init();  // error: alas, no constructor is visible
      var d := new X.D;  // error: even though D has no constructor, the absence of imported constructor does not let us conclude there aren't any
    }
  }
}

module K {
  module Y {
    export
      reveals C provides C.Valid, C.Init, C.Print, C.G

    class C {
      predicate Valid() { true }
      constructor Init() ensures Valid() { }
      method Print() requires Valid() { }
      function G(): nat requires Valid() { 5 }
    }
  }

  method M() {
    var c := new Y.C.Init();
    assert c.Valid() ==> 0 <= c.G();
    c.Print();
  }
}

module L {
  module Z {
    export
      provides C.Init, C.Print
      reveals C, C.Valid, C.G

    class C {
      predicate Valid() { true }
      constructor Init() ensures Valid() { }
      method Print() requires Valid() { }
      function G(): nat requires Valid() { 5 }
    }
  }

  method M() {
    var c := new Z.C.Init();
    assert c.Valid() ==> 0 <= c.G();
    c.Print();
  }
}

module M {
  module W {
    export
      provides C.Valid, C.Print, C.G
      reveals C  // by revealing a class, the anonymous constructor (if any) is also provided

    class C {
      predicate Valid() { true }
      constructor () ensures Valid() { }  // anonymous constructor
      method Print() requires Valid() { }
      function G(): nat requires Valid() { 5 }
    }
  }

  method M() {
    var c := new W.C();
    assert c.Valid() ==> 0 <= c.G();
    c.Print();
  }
}

module N {
  module NN {
    export 050
      reveals 300, C.4
      provides C
    export
      reveals 300, C.7
      provides C
    function 300(): int { 297 }
    class C {
      function 4(): int { 4 }
      static const 7 := 6
    }
  }
  module MM {
    import A = NN
    import B = NN`050
    import opened D = NN
    method X() {
      ghost var f := A.300;
      assert f() == 297 == A.300();
      ghost var s := C.7;
      assert s == C.7 == 6 == B.C.7;
    }
  }
}

module ModuleName0 {
  export X reveals pi
  const pi := 3.14
  type U = X  // error: X is not a type
}
module ModuleName1 {
  export X reveals pi
  const pi := 3.14
  // regression test:
  type X = int  // fine, because export names are in a different name space than other module contents
}
module ModuleName2 {
  export X reveals pi
  const pi := 3.14
  const X := 17  // fine, because export names are in a different name space than other module contents
}
module ModuleName3 {
  export X reveals pi
  const pi := 3.14
  function X(): int { 17 }  // fine, because export names are in a different name space than other module contents
}
module ModuleName4 {
  export X reveals pi
  const pi := 3.14
  method X() { }  // fine, because export names are in a different name space than other module contents
}
module ModuleName5 {
  export X reveals e
  const e := 2.7
  import X = ModuleName4`X  // fine, because export names are in a different name space than other module contents
  datatype Dt = Make(pi: int)
  const X := Make(10)  // X is duplicate here and as local name of (aliased) module
  method Test() {
    assert X.pi == 10;  // X.pi refers to member pi of const X, not to the imported ModuleName4.pi
  }
}
module ModuleName6 {
  // regression: the error in the next line should be reported there, not in ModuleName4 above
  import X = ModuleName4  // error: ModuleName4 does not have an eponymous export set
}
module ModuleName7 {
  import X = ModuleName4`Y  // error: ModuleName4 does not have an export set named Y
}
module ModuleName8 {
  export X reveals pi
  export X reveals e  // error: duplicate name of export set
  const pi: int
  const e: int
}

module ExportCycle0 {
  export extends A // error: export cycle
  export A extends B
  export B extends ExportCycle0
}

module ExportCycle1 {
  export A extends B // error: export cycle
    provides X
  export B extends C
    reveals X
  export C extends A
    provides X
  type X = int
}
