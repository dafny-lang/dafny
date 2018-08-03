// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function method {:simplifier} simp<T>(t: T): T { t }

datatype List<T> = Cons(car: T, cdr: List<T>) | LNil

datatype Option<T> = Some(val: T) | None

datatype Pair<T,U> = Pair(car: T, cdr: U)

function method {:opaque} AssocGet<T(==),U>(l: List<Pair<T,U>>, x: T): Option<U>
    decreases l
{
    if l.LNil? then None else
    if l.car.car == x then Some(l.car.cdr) else
    AssocGet(l.cdr, x)
}

lemma {:simp} AssocGet_Cons<K, V>(x: K, v: V, ps: List<Pair<K, V>>, k: K)
  ensures
  AssocGet(Cons(Pair(x, v), ps), k) ==
  if x == k then Some(v) else AssocGet(ps, k)
{
  reveal AssocGet();
}

method test(x: int) {
  assert simp(AssocGet(Cons(Pair("x", x), LNil), "x")) == Some(x);
}
