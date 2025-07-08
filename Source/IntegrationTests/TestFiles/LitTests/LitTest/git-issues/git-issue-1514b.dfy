// RUN: %testDafnyForEachCompiler "%s" -- --type-system-refresh=false --general-newtypes=false --standard-libraries --relax-definite-assignment

import opened Std.Wrappers

trait Foo<C, D> {
  method Bar(a: C) returns (r: D)
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
  method Bar(a: string) returns (r: Option<string>) {
    return Some(a);
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
