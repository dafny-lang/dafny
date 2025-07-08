// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --allow-axioms --standard-libraries --relax-definite-assignment

import opened Std.Wrappers

trait Foo<C, D> {
  function Bar(a: C): (r: D)
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
  function Bar(a: string): (r: Option<string>) {
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
