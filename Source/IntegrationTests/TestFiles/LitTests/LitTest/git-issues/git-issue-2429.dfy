// RUN: %verify --allow-axioms --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost predicate P<A>(s: seq<A>)

trait T<A> extends object {
  method M(a: A)
    requires Q([a][0 := a])
    modifies if P([a][0 := a]) then {} else {this}
    ensures P([a][0 := a])
    decreases if P([a][0 := a]) then 3 else 4
  ghost function F(a: A): int
    requires Q([a][0 := a])
    reads if P([a][0 := a]) then {} else {this}
    ensures F(a) == 5 ==> P([a][0 := a])
    decreases if P([a][0 := a]) then 3 else 4
}

ghost predicate Q<A>(s: seq<A>)
  ensures Q(s) ==> P(s)

class C extends T<object> {
  // A missing type substitution in the translator used to cause issues here:
  method M(a: object)
    requires P([a][0 := a])
    modifies if Q([a][0 := a]) then {} else {this}
    ensures Q([a][0 := a])
    decreases if Q([a][0 := a]) then 3 else 2
  ghost function F(a: object): int
    requires P([a][0 := a])
    reads if Q([a][0 := a]) then {} else {this}
    ensures F(a) == 5 ==> Q([a][0 := a])
    decreases if Q([a][0 := a]) then 3 else 4
}
