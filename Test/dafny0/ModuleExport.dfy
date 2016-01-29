// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
	default export Public { f, h}
	export E1 { f, g}
	export E2 extends Public, E1 {T}
  export Friend extends Public {g, T}
	export Fruit {Data}

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
  import X = A.Public
	method m() {
	  X.h();  // OK
	  assert X.f() == 818; // OK
		assert X.g() == 819; // error
		assert X.k() == 820; // error
		X.T.l(); // error
	}
}

module C {
  import X = A.Friend
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
  import opened A.Fruit

  function G(d: Data): int
    requires d != Data.Lemon
  {
    match d
    case Lemon => G(d)
    case Kiwi(x) => 7
		case Orang => 8  // error
  } 
}