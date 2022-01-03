// RUN: %dafny /compile:3 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../libraries/src/Wrappers.dfy"
import opened Wrappers

trait Foo<C, D> {
  function method Bar(a: C): (r: D)
}

type FooWithResult<A, B> = Foo<A, Option<B>>

method Bar<E, F>(
  a: E,
  foo: FooWithResult<E, F>
) returns (r: Option<F>) {
  var res :- foo.Bar(a);
}