// RUN: %exits-with 2 %verify --reads-clauses-on-methods "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module CContainer {
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
}

abstract module MyAbstractModule {
  class C { var u : int }
  method M(c: C) returns (r: int)
  {}
}

module MyRefinedModule refines MyAbstractModule {
  method M(c: C) returns (r: int)
    reads c // Error: a refining method is not allowed to extend the reads clause
  {}
}