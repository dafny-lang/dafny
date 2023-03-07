// RUN: %dafny /compile:0 /proverOpt:O:smt.qi.eager_threshold=30 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module NeedsAllLiteralsAxiom {
  // The following test shows that there exist an example that
  // benefits from the all-literals axiom.  (It's not clear how
  // important such an example is, nor is it clear what the cost
  // of including the all-literals axiom is.)

  function trick(n: nat, m: nat): nat
    decreases n;  // note that m is not included
  {
    if n < m || m==0 then n else trick(n-m, m) + m
  }

  lemma lemma_trick(n: nat, m: nat)
    ensures trick(n, m) == n;
  {
  }

  lemma calc_trick(n: nat, m: nat)
    ensures trick(100, 10) == 100;
  {
  }
}
