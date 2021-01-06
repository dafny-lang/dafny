// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype T = T(x: int)
datatype S = S(u: int, v: int, w: int, x: int, y: int, z: int)

predicate a(t: T)
predicate b(t: T)
predicate c(t: T)
predicate d(t: T)
predicate e(t: T)
predicate f(t: T)
predicate g(t: T)

predicate WellFormed(t: T) {
  && a(t)
}

function Func(t: T) : S
requires WellFormed(t)
{
  S(t.x, t.x, t.x, t.x, t.x, t.x)
}

predicate Good(s: S) {
  && s.u == 5
  && s.v == 5
  && s.w == 5
  && s.x == 5
  && s.y == 5
  && s.z == 5
}

function {:opaque} GetT() : T {
  T(5)
}

lemma foo()
  ensures var t := GetT();
    && WellFormed(t)
    && Good(Func(t))
{
  reveal_GetT();
}

