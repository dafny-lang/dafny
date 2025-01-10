// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var u : int

  constructor(u: int) reads {} {
    this.u := u;
  }

  constructor Copy(c: C) reads c {
    this.u := c.u;
  }

  method M() reads {} {}

  static method TrexsCantSeeIt(c: C) reads c {}

  ghost method OoooSpooky() reads {} {}

  lemma Lemma() reads * {}

  twostate lemma TwostateLemma() reads {} {}

  greatest lemma BestLemmaEver(c: C) reads c {}

  least lemma ICanBarelySeeIt(c: C) reads c {}
}
