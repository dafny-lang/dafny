// RUN: %dafny /compile:0 /rprint:"%t.rprint" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<T> = Nil | Cons(hd: T, tl: List)


// ---------------------------------------------------

// The followinng functions and methods are oblivious of the fact that
// List takes a type parameter (except Lemma, which needs it).

function concat(xs: List, ys: List): List
{
  match xs
  case Nil => ys
  case Cons(x, tail) => Cons(x, concat(tail, ys))
}

function reverse(xs: List): List
{
  match xs
  case Nil => Nil
  case Cons(t, rest) => concat(reverse(rest), Cons(t, Nil))
}

lemma Lemma<A>(xs: List, ys: List)
  ensures reverse(concat(xs, ys)) == concat(reverse(ys), reverse(xs))
{
  match xs
  case Nil =>
    assert forall ws: List<A> {:induction} :: concat(ws, Nil) == ws;
  case Cons(t, rest) =>
    assert forall a: List<A>, b, c {:induction} :: concat(a, concat(b, c)) == concat(concat(a, b), c);
}