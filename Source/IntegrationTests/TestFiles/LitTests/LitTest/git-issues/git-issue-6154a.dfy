// RUN: %testDafnyForEachResolver "%s"

datatype List<X> = Nil | Cons(head: X, tail: List<X>)

lemma Test<X, Y>(xs: List<X>, y: Y) {
  // the > in the following line once used to crash the resolver
  assert y < xs <==> xs > y;
}
