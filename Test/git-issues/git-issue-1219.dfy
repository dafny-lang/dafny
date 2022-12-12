// RUN: %exits-with 2 %dafny /print:"%t.print" /dprint:- /env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Issue1219 {
  datatype CheckRussell = ISet(s: iset<CheckRussell>)  // error: recursive mentions must be used in a strict (and covariant) context

  lemma russell_paradox()
    ensures false
  {
    var t := ISet(iset t: CheckRussell | t !in t.s );
    assert t in t.s;
    assert t !in t.s;
  }
}

// ------ a function and (regression!) a type synonym

module RegressionSynonymDependencies {
  // regression: the synonym type DD was once not been placed in the SCC of D and F, which had caused no error to be reported
  type DD = D
  type F = DD -> bool // error: this increases cardinality
  datatype D = Ctor(f: F)

  lemma False()
    ensures false
  {
    var f := (d: D) => !d.f(d);
    var dd := Ctor(f);
    assert f(dd);
    assert !f(dd);
  }
}

module GeneralFunction0 {
  type DD = D
  datatype D = Ctor(f: DD ~> bool) // error: this use of DD increases cardinality

  lemma False()
    ensures false
  {
    var f := (d: D) => !d.f(d);
    var dd := Ctor(f);
    assert f(dd);
    assert !f(dd);
  }
}

module GeneralFunction1 {
  datatype D = Ctor(f: D ~> bool) // error: violates strict positivity

  lemma False()
    ensures false
  {
    var f := (d: D) => !d.f(d);
    var dd := Ctor(f);
    assert f(dd);
    assert !f(dd);
  }
}
