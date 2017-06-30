// RUN: %dafny /env:0 /dprint:"%t.dprint" /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
	export A reveals f provides h
	export E1 provides f reveals g
	export E2 extends A, E1 reveals T
  export Friend extends A reveals g, T
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
