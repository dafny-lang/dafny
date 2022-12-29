// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module M0 {
  type A
  type B = int
  type C(==)
  type D(==)
  type E(==)
  type F(==)

  type G
  type H<X,Y>
  type J<Z>

  type K0<W(==)>
  type K1<W(==)>
  type L<V>
  type M(==)<U>
  type N(==)<U>
  type O(==)<U>
  type P<U>
  type R<U>
  type S<U>
  type T

  type TP0
  type TP1<Y0>
  type TP2<Y0,Y1>
}
module M1 refines M0 {
  type A = int
  type B  // error: cannot change a type synonym into an opaque type
  datatype C = MakeC(ghost x: int, y: int)  // error: this type does not support equality
  type D = C  // error: this type does not support equality
  codatatype E = More(bool, E)  // error: this type does not support equality
  datatype List<T> = Nil | Cons(T, List)
  type F = List<real>  // fine

  type G<X0> = List<X0>  // error: G is not allowed to take type parameters
  type H<X1> = List<X1>  // error: H needs two type parameters
  type J = List<real>  // error: J needs one type parameter

  type K0<W> = List<W>  // error: change in (==)
  type K1<W>  // error: change in (==)
  type L<V(==)> = List<V>  // error: change in (==)
  type M<U'> = int  // fine, because M<U'> does support equality
  type N<U'> = List<U'>  // error: N<U'> does not support equality
  type O<U'(==)> = List<U'>  // error: change in (==)
  type P<U'> = List<U'>  // fine
  class R { }  // error: wrong number of type arguments
  class S<T> { }  // error: not allowed to rename type parameter (U -> T)
  class T<T> { }  // error: wrong number of type arguments

  type TP0<E0>  // error: wrong number of type arguments
  type TP1  // error: wrong number of type arguments
  type TP2<Y0, E1>  // error: not allowed to rename type parameter (Y1 -> E1)
}

module ListLibrary {
  datatype List<T> = Nil | Cons(T, List)
}

module DatatypeTestX {
  import MyList = ListLibrary
  method Test() {
    var a: MyList.List<real> := MyList.Nil;
    var b: MyList.List<real> := MyList.List.Nil;
    var c: MyList.List<real> := MyList.List<int>.Nil;  // error: incompatible types
    var d: MyList.List<real> := MyList.List<real>.Nil;
  }
}

module DatatypeTestY {
  import MyList = ListLibrary
  method Test() {
    var a: MyList.List<real> := MyList.Nil;
    var b: MyList.List<real> := MyList.List.Nil;
    var d: MyList.List<real> := MyList.List<real>.Nil;

    var w: MyList.List := MyList.Nil;  // error: underspecified type argumement
    var x: MyList.List := MyList.List.Nil;  // error: underspecified type argumement
    var y: MyList.List := MyList.List<int>.Nil;
    var z: MyList.List := MyList.List<real>.Nil;

    var e := MyList.List.Nil;
    var f: MyList.List<real> := e;
  }
}

module DatatypeTestLocalX {
  datatype List<T> = Nil | Cons(T, List)
  method Test() {
    var a: List<real> := Nil;
    var b: List<real> := List.Nil;
    var c: List<real> := List<int>.Nil;  // error: incompatible types
    var d: List<real> := List<real>.Nil;
  }
}

module DatatypeTestLocalY {
  datatype List<T> = Nil | Cons(T, List)
  method Test() {
    var a: List<real> := Nil;
    var b: List<real> := List.Nil;
    var d: List<real> := List<real>.Nil;

    var w: List := Nil;  // error: underspecified type argumement
    var x: List := List.Nil;  // error: underspecified type argumement
    var y: List := List<int>.Nil;
    var z: List := List<real>.Nil;

    var e := List.Nil;
    var f: List<real> := e;
  }
}

module ClassLibrary {
  class Classic<A> {
    static function method F(): A
  }
}

module ClassTestX {
  import C = ClassLibrary
  method Test() {
    var x: C.Classic<real> := C.Classic<int>.F();  // error: incompatible types
  }
}

module ClassTestY {
  import C = ClassLibrary
  method Test() {
    var a := C.Classic<int>.F();
    var b: real := C.Classic.F();
    var c: C.Classic<real> := C.Classic.F();  // here, the RHS type parameter is instantiated with C.Classic<real>, which is fine
    var d := C.Classic.F();  // error: underspecified type
  }
}
