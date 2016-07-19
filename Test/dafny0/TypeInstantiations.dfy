// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
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

  type K0<W> = List<W>
  type K1<W>
  type L<V(==)> = List<V>  // fine
  type M<U'> = int  // fine, because M<U'> does support equality
  type N<U'> = List<U'>  // error: N<U'> does not support equality
  type O<U'(==)> = List<U'>  // fine
  type P<U'> = List<U'>  // fine
  class R { }  // error: wrong number of type arguments
  class S<T> { }
  class T<T> { }  // error: wrong number of type arguments

  type TP0<E0>  // error: wrong number of type arguments
  type TP1  // error: wrong number of type arguments
  type TP2<E0,E1>
}
