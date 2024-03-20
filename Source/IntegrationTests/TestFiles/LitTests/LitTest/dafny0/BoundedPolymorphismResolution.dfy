// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"

module BadTypeNames {
  datatype DT<W extends Unknown> = Dt(w: W) // error: what is Unknown?

  type Syn<X extends Unknown> = DT<X> // error: what is Unknown?

  class Class<Y extends Unknown> { // error: what is Unknown?
  }

  trait AnotherTrait<Z extends Unknown> { // error: what is Unknown?
  }

  type Abstract<V extends Unknown> // error: what is Unknown?

  trait Generic<Q> { }

  codatatype Mutual<A extends Generic<Z>, B extends Generic<A>> = More(Mutual) // error: what is Z?

  function Function<K extends Unknown>(k: K): int { 2 } // error: what is Unknown?

  method Method<L extends Unknown>(l: L) { } // error: what is Unknown?

  least predicate Least<M extends Unknown>(m: M) { true } // error: what is Unknown?

  greatest lemma Greatest<N extends Unknown>(n: N) { } // error: what is Unknown?

  iterator Iter<O extends Unknown>(o: O) { } // error: what is Unknown?
}
