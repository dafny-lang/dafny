// RUN: %dafny /compile:0 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../libraries/src/Wrappers.dfy"
import opened Wrappers

datatype Bar = Bar(i: string)
function method ParseBar(s: string): Result<Bar, string> {
   Success(Bar(s))
}

class Foo {
  const bar: Bar

  constructor (
    barLike: string
  )
    requires ParseBar(barLike).Success?
  {
      this.bar :- assert ParseBar(barLike);
  }
}