// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The axiom for the ORDINAL expression (o - m) + n carried the guard of (o + m) - n,
// n <= o.Offset + m, so it also applied where o - m is not defined, and there it said
// something false. A program cannot state such a term: o - m is well-formed only when
// m <= o.Offset, and constant ordinal arithmetic is folded before it reaches the solver.
// So no program is known to prove false by it; the axioms themselves had no model (see
// the issue). The guard is now m <= o.Offset. With it the axiom also applies where it
// holds and did not apply before, when n exceeds o.Offset + m:

lemma MinusThenPlus(o: ORDINAL, m: nat, n: nat)
  requires m <= o.Offset && o.Offset + m < n
  ensures (o - (m as ORDINAL)) + (n as ORDINAL) == o + ((n - m) as ORDINAL)
{
}

lemma MinusThenPlusLess(o: ORDINAL, m: nat, n: nat)
  requires n <= m <= o.Offset
  ensures (o - (m as ORDINAL)) + (n as ORDINAL) == o - ((m - n) as ORDINAL)
{
}
