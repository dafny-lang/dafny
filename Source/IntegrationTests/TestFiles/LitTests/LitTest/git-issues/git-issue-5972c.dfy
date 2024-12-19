// RUN: %exits-with 2 %baredafny verify %args --type-system-refresh --general-newtypes "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype FunMap<T> = s: map<int, int -> T> | true {}

datatype A<T> = A(a: FunMap<T>)

method Test<T(==)>() {

}

method Main() {
  Test<A<int>>(); // Error: A<int> does not support equality
}