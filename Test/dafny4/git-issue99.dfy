// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module TestModule {
  lemma lemma_Test<T1, T2>(x2:T2, s:iset<(T1, T2)>)
    requires exists c:BOGUS_TYPE :: (c, x2) in s;  // error (x2), both resulting from an unidentified type
  {
  }
}
