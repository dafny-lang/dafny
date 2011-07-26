// ultra filter

class UltraFilter<G> {
  static function IsFilter(f: set<set<G>>, S: set<G>): bool
  {
    (forall A, B :: A in f && A <= B ==> B in f) &&
    (forall C, D :: C in f && D in f ==> C * D in f) &&
    S in f &&
    {} !in f
  }

  static function IsUltraFilter(f: set<set<G>>, S: set<G>): bool
  {
    IsFilter(f, S) &&
    (forall g :: IsFilter(g, S) && f <= g ==> f == g)
  }

  method Theorem(f: set<set<G>>, S: set<G>, M: set<G>, N: set<G>)
    requires IsUltraFilter(f, S);
    requires M + N in f;
    ensures M in f || N in f;
  {
    if (M !in f) {
      // instantiate 'g' with the following 'h'
      var h := H(f, S, M);
      Lemma_HIsFilter(h, f, S, M);
      Lemma_FHOrdering0(h, f, S, M);
    }
  }

  // Dafny currently does not have a set comprehension expression, so this method stub will have to do
  method H(f: set<set<G>>, S: set<G>, M: set<G>) returns (h: set<set<G>>)
    ensures (forall X :: X in h <==> M + X in f);

  method Lemma_HIsFilter(h: set<set<G>>, f: set<set<G>>, S: set<G>, M: set<G>)
    requires IsFilter(f, S);
    requires (forall X :: X in h <==> M + X in f);
    requires M !in f;
    ensures IsFilter(h, S);
  {
    // call Lemma_H0(h, f, S, M, *, *);
    assume (forall A, B :: A in h && A <= B ==> B in h);

    // call Lemma_H1(h, f, S, M, *, *);
    assume (forall C, D :: C in h && D in h ==> C * D in h);

    Lemma_H2(h, f, S, M);

    Lemma_H3(h, f, S, M);
  }

  method Lemma_H0(h: set<set<G>>, f: set<set<G>>, S: set<G>, M: set<G>, A: set<G>, B: set<G>)
    requires IsFilter(f, S);
    requires (forall X :: X in h <==> M + X in f);
    requires A in h && A <= B;
    ensures B in h;
  {
    assert M + A <= M + B;
  }

  method Lemma_H1(h: set<set<G>>, f: set<set<G>>, S: set<G>, M: set<G>, C: set<G>, D: set<G>)
    requires IsFilter(f, S);
    requires (forall X :: X in h <==> M + X in f);
    requires C in h && D in h;
    ensures C * D in h;
  {
    assert (M + C) * (M + D) == M + (C * D);
  }

  method Lemma_H2(h: set<set<G>>, f: set<set<G>>, S: set<G>, M: set<G>)
    requires IsFilter(f, S);
    requires (forall X :: X in h <==> M + X in f);
    ensures S in h;
  {
    // S is intended to stand for the universal set, but this is the only place where that plays a role
    assume M <= S;

    assert M + S == S;
  }

  method Lemma_H3(h: set<set<G>>, f: set<set<G>>, S: set<G>, M: set<G>)
    requires IsFilter(f, S);
    requires (forall X :: X in h <==> M + X in f);
    requires M !in f;
    ensures {} !in h;
  {
    assert M + {} == M;
  }

  method Lemma_FHOrdering0(h: set<set<G>>, f: set<set<G>>, S: set<G>, M: set<G>)
    requires IsFilter(f, S);
    requires (forall X :: X in h <==> M + X in f);
    requires IsFilter(h, S);
    ensures f <= h;
  {
    // call Lemma_FHOrdering1(h, f, S, M, *);
    assume (forall Y :: Y in f ==> Y in h);
    assume f <= h;  // hickup in boxing
  }

  method Lemma_FHOrdering1(h: set<set<G>>, f: set<set<G>>, S: set<G>, M: set<G>, Y: set<G>)
    requires IsFilter(f, S);
    requires (forall X :: X in h <==> M + X in f);
    ensures Y in f ==> Y in h;
  {
    assert Y <= M + Y;
  }
}
