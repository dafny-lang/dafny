// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"

module A {
  type R<T, U> = T

  datatype D<U> = D(x: R<string, U>)

  method Foo<U>(x: R<string, U>)
  {
    var _ := D(x);
  }
}

module B {
  type MyType<X>

  type R<T, U> = T

  datatype D<U> = D(x: R<MyType<char>, U>)

  method Foo(x: R<MyType<char>, real>)
  {
    var y := D<bool>.D(x);
  }
}
