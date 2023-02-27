// RUN: %dafny /compile:3 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "Wrappers.dfy"
import opened Wrappers

trait Foo<C, D> {
  function method Bar(a: C): (r: D)
}

type FooWithResult<A, B> = Foo<A, Option<B>>

method Bar<E, F>(
  a: E,
  foo: FooWithResult<E, F>
) returns (r: Option<F>) {
  r := None;
  var res :- foo.Bar(a);
  r := Some(res);
}

class ConcreteFoo extends Foo<string, Option<string>> {
  constructor () {}
  function method Bar(a: string): (r: Option<string>) {
    Some(a)
  }
}

method Main() {
  var t := new ConcreteFoo();
  var x := Bar("ok", t);
  if x.Some? {
    print x.value;
  } else {
    print "None?!";
  }
}
