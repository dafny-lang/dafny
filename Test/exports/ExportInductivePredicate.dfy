// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  least predicate P(x: int)
  {
    x < 100
  }

  greatest predicate Q(x: int)
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

  least lemma V(x: int)
    requires P(x)
  {
  }
  least lemma W(x: int)
    requires M.P(x)
  {
  }
  greatest lemma CoV(x: int)
    requires x < 100
    ensures Q(x)
  {
  }
  greatest lemma CoW(x: int)
    requires x < 100
    ensures M.Q(x)
  {
  }
}
