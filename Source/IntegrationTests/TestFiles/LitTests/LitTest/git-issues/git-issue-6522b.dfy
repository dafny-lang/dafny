// RUN: %testDafnyForEachResolver "%s"

// A quantifier in an extreme lemma's specification does not stop the predicate calls under it
// from becoming prefix-predicate calls in the prefix lemma, whatever the quantified type

datatype S = N(o: ORDINAL) | Top

greatest predicate G(s: S) {
  s.N? && G(N(s.o + 1))
}

greatest lemma L(s: S)
  requires s.N?
  ensures exists t: S :: t.N? && t.o == s.o && G(t)
{
  L(N(s.o + 1));
}
