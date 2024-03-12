// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type uint8 = i | 0 <= i <= 255

datatype Thing = Thing
type Foo =  s: seq<uint8> | |s| < 10 witness *
type Fii =  real 

function {:axiom} Bar(t: Thing): Foo
function {:axiom} Bii(t: Thing): Fii

predicate {:axiom} Baz(f: Thing -> seq<uint8>)

predicate compose() {
  Baz(Bar)
}
predicate compose2() {
  Baz(Bii)
}
