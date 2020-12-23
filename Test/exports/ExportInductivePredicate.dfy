// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  inductive predicate P(x: int)
  {
    x < 100
  }

  copredicate Q(x: int)
  {
    x < 100
  }

  lemma K(x: int)
    requires P(x)
  {
  }
  lemma K'(x: int)
    requires P#[3](x)
  {
  }
  lemma CoK(x: int)
    requires x < 100
    ensures Q(x)
  {
  }
  lemma CoK'(x: int)
    requires x < 100
    ensures Q#[3](x)
  {
  }
}

module M' {
  import opened M

  lemma H(x: int)
    requires M.P(x)
  {
  }
  lemma H'(x: int)
     requires M.P#[3](x)
  {
  }
  lemma CoH(x: int)
    requires x < 100
    ensures M.Q(x)
  {
  }
  lemma CoH'(x: int)
    requires x < 100
    ensures M.Q#[3](x)
  {
  }

  lemma L(x: int)
    requires P(x)
  {
  }
  lemma L'(x: int)
    requires P#[3](x)
  {
  }
  lemma CoL(x: int)
    requires x < 100
    ensures Q(x)
  {
  }
  lemma CoL'(x: int)
    requires x < 100
    ensures Q#[3](x)
  {
  }

  inductive lemma V(x: int)
    requires P(x)
  {
  }
  inductive lemma W(x: int)
    requires M.P(x)
  {
  }
  colemma CoV(x: int)
    requires x < 100
    ensures Q(x)
  {
  }
  colemma CoW(x: int)
    requires x < 100
    ensures M.Q(x)
  {
  }
}
