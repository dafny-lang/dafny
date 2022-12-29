// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This program shows how to model an outer type whose invariant refers to the invariant of an inner type.

// A universe of objects playing under LCI rules 
trait S {
  // The set of objects in the universe
  ghost var obs: set<O>

  // Workaround Dafny not supporting _ as object
  function upCast(o: object): object {o}
  
  // Universe invariant: the universe doesn't contain itself, 
  // and its objects in this universe agree that they are in this universe.
  // We define this to allow a generic object operation (O.join below) to add the object to the universe, 
  // without having to check the object invariants.
  predicate i0() reads this, obs { forall o: O | o in obs :: o.s == this && upCast(o) != this }
  
  // Global 1-state invariant: all objects satisfy their individual invariants.
  predicate i() reads * { i0() && forall o: O | o in obs :: o.i() }
  
  // Global 2-state invariant: all old objects satisfy their 2-state invariants.
  twostate predicate i2() reads * { forall o: O | o in old(obs) :: o in obs && o.i2() }
  
  // The first condition for legality: old objects that change a field must obey their 1- and 2-state invariants.
  twostate predicate legal0() reads * { forall o: O | o in old(obs) :: unchanged(o) || (o.i2() && o.i()) }
  
  // The second condition for legality: new objects must satisfy their invariants.
  twostate predicate legal1() reads * { forall o: O | o in obs && o !in old(obs) :: o.i() }
  
  // A legal transition is one that starts from a good state, preserves the universe invariant, and meets the legality conditions. 
  twostate predicate legal() reads * { old(i()) && i0() && old(obs) <= obs && legal0() && legal1() }
  
  // LCI soundness: legal transitions are good. This makes use of the admissibility obligations build into O's.
  twostate lemma lci() requires legal() ensures i() && i2() {
    forall o: O | o in old(obs) && o.admPre() ensures o.i2() && o.i() { o.adm(); }
  }
}

// A generic object trait
trait O {
  // Universe of which O is a member.
  // This should really be a constant, but I don't know how to do that while factoring out join below,
  // because traits can't have constructors.
  ghost const s: S

  // Base invariant: we're in the universe, and the universe satisfies its base.
  predicate i0() reads * { this in s.obs && s.i0() }
  
  // Join universe s
  ghost method join()
    requires s.i0() && s.upCast(this) != s
    modifies s 
    ensures i0() && s.obs == old(s.obs) + { this }
  {
    s.obs := s.obs + { this }; 
  }

  // Precondition for the admissibility check.
  // This is broken into a separate predicate because Dafny currently doesn't allow adm.requires() in a 1-state context
  twostate predicate admPre() reads * { i0() && old(i0() && s.i()) && unchanged(this) && s.legal() }

  // Global invariant (from o's perspective) - I am in the universe and the universe is good. (This implies I am good also.)
  predicate gi() reads * { i0() && s.i() }

  // Global 2-state invariant (from o's perspective).
  twostate predicate gi2() requires old(gi()) reads * { i0() && s.i2() }

  // To be implemented in the class: 1-state invariant, 2-state invariant, and admissibility proof.
  predicate i() reads *
  twostate predicate i2() reads *
  twostate lemma adm() requires admPre() ensures i2() && i()
}

class Inner extends O {
  var data: int

  // Invariant
  predicate i() reads * {
    && i0()
  }
  twostate predicate i2() reads * {
    && old(data) <= data
  }

  twostate lemma adm() {}

  constructor (ghost s: S, initial_data: int)
    requires s.i()
    modifies s
    ensures s.i()
  {
    this.s := s;
    data := initial_data;
    new;
    join();
    s.lci();
  }
}

class Outer extends O {
  var inner: Inner

  // Invariant
  predicate i() reads * {
    && i0()
    && s == inner.s
    && inner.i()
  }
  twostate predicate i2() reads * {
    && inner == old(inner)
    && inner.i2()
  }

  twostate lemma adm() requires admPre() ensures i2() && i() {
  }

  constructor (ghost s: S, inner: Inner)
    requires s.i() && s == inner.s && inner.i()
    modifies s
    ensures s.i()
  {   
    this.s := s;
    this.inner := inner;
    new;
    join();
    s.lci();
  }
}
