// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism --type-system-refresh --general-traits=full "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: windows

datatype I_<T, U> = I_(t: T, u: U)

type I<T, U> = x: I_<T, U> | true witness *

datatype {:rust_rc false} A<T, U> = A(B: I<T, U>)

datatype {:rust_rc false} M_<K, V> = M_(m: map<K, V>)

type M<K, V> = x: M_<K, V> | true witness *

trait O<K(==), E(==), V, D> {}

datatype U<K, E, V, D> = U(o: O<int, E, V, D>)

datatype G<K, E, V> = G(m1: map<K, K>, m2: map<K, E>, m3: map<K, V>)

type F<K, E, V> = g: G<K, E, V> | true witness *

datatype V<K, T> = V(u: U<K, int, T, F<int, int, T>>)

datatype Phantom<T> = Phantom()

datatype WithGhost_ = WithGhost(i: int, ghost n: int)

type WithGhost = x: WithGhost_ | true witness *

datatype {:rust_rc false} WithGhostWrapper = WithGhostWrapper(r:WithGhost)

type DoubleWithGhost = t:(WithGhostWrapper,WithGhostWrapper) | true witness *

datatype {:rust_rc false} DoubleWithGhostWrapper = DoubleWithGhostWrapper(
    dwg:DoubleWithGhost
)

datatype Wrapper1<T> = Wrapper1(w1: T)
datatype Wrapper2<T> = Wrapper2(w2: T)
datatype Wrapper3<S> = Wrapper3(w21: Wrapper2<Wrapper1<S>>) {
  function ReturnThis(f: Wrapper3<S> -> Wrapper3<S>): Wrapper3<S> {
    f(this)
  }
}

method Test<T(==)>() {
}

method Main() {
  Test<M<int, int>>();
  Test<A<int, int>>();
  Test<I<int, int>>();
  Test<I_<int, int>>();
  Test<A<M<int, int>, int>>();
  Test<V<int, int>>();
  //Test<Phantom<int -> int>>();
  print "ok";
}