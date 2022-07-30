// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P<A>(s: seq<A>)

trait T<A> {
  method M(a: A) ensures P([a][0 := a])
}

predicate Q<A>(s: seq<A>)
  ensures Q(s) ==> P(s)

class C extends T<object> {
  // A missing type substitution in the translator used to cause issues here:
  method M(a: object) ensures Q([a][0 := a])
}
