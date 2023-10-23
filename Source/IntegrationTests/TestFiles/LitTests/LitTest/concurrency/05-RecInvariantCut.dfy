// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This program shows how to model two types A and B with mutually recursive invariants.

// Cast a trait type to an object type.
// Dafny doesn't allow to do reference equality between a trait and an object type, so we use this function to upcast where needed.
ghost function upCast(o: object): object {o}

// A universe of objects playing under LCI rules 
trait Universe {
  // The set of objects in the universe
  ghost var content: set<Object>

  // Universe invariant: the universe doesn't contain itself, 
  // and its objects in this universe agree that they are in this universe.
  // We define this to allow a generic object operation (O.join below) to add the object to the universe, 
  // without having to check the object invariants.
  ghost predicate globalBaseInv() reads this, content {
    forall o: Object | o in content :: o.universe == this && upCast(o) != this
  }
  
  // Global 1-state invariant: all objects satisfy their individual invariants.
  ghost predicate globalInv() reads * {
    globalBaseInv() && forall o: Object | o in content :: o.inv()
  }
  
  // Global 2-state invariant: all old objects satisfy their 2-state invariants.
  twostate predicate globalInv2() reads * {
    forall o: Object | o in old(content) :: o in content && o.inv2()
  }
  
  // A legal transition is one that starts from a good state, preserves the universe invariant, and meets the legality conditions. 
  twostate predicate legalTransition() reads * {
    && old(globalInv())
    && globalBaseInv()
    && old(content) <= content
    // The first condition for legality: old objects that change a field must obey their 1- and 2-state invariants.
    && (forall o: Object | o in old(content) :: unchanged(o) || (o.inv2() && o.inv()))
    // The second condition for legality: new objects must satisfy their invariants.
    && (forall o: Object | o in content && o !in old(content) :: o.inv())
  }
  
  // LCI soundness: legal transitions are good. This makes use of the admissibility obligations build into Object's.
  twostate lemma lci()
    requires legalTransition()
    ensures globalInv() && globalInv2()
  {
    forall o: Object | o in old(content) && o.goodPreAndLegalChanges() ensures o.inv2() && o.inv() { o.adm(); }
  }
}

// A generic object trait
trait Object {
  // Universe of which the Object is a member.
  // This should really be a constant, but I don't know how to do that while factoring out join below,
  // because traits can't have constructors.
  ghost const universe: Universe

  // Base invariant: we're in the universe, and the universe satisfies its base.
  ghost predicate baseInv() reads * { this in universe.content && universe.globalBaseInv() }
  
  // Join the universe
  ghost method join()
    requires universe.globalBaseInv() && upCast(this) != universe
    modifies universe 
    ensures baseInv() && universe.content == old(universe.content) + { this }
  {
    universe.content := universe.content + { this }; 
  }

  // Precondition for the admissibility check.
  // This is broken into a separate predicate because Dafny currently doesn't allow adm.requires() in a 1-state context
  twostate predicate goodPreAndLegalChanges() reads * {
    && old(baseInv() && universe.globalInv())
    && baseInv()
    && unchanged(this)
    && universe.legalTransition()
  }

  // Global invariant (from o's perspective) - I am in the universe and the universe is good. (This implies I am good also.)
  ghost predicate globalInv() reads * { baseInv() && universe.globalInv() }

  // Global 2-state invariant (from o's perspective).
  twostate predicate globalInv2() requires old(globalInv()) reads * { baseInv() && universe.globalInv2() }

  // To be implemented in the class: 1-state invariant, 2-state invariant, and admissibility proof.
  ghost predicate inv() reads *
  twostate predicate inv2() reads *
  twostate lemma adm() requires goodPreAndLegalChanges() ensures inv2() && inv()
}

class A extends Object {
  ghost var valid: bool // Like in VCC
  ghost var b: B

  ghost predicate inv() reads * {
    && localInv()
    && (valid ==> b.localInv())
  }
  ghost predicate localInv() reads * {
    && baseInv()
    && universe == b.universe
    && (valid ==>
      && b.valid
      && b.a == this
      //&& b.inv() // Cut recursion
    )
  }

  twostate predicate inv2() reads * {
    && localInv2()
    && (old(valid) ==> b.localInv2())
  }
  twostate predicate localInv2() reads * {
    && (old(valid) ==>
      && valid // This makes deallocation impossible
      && old(b) == b
      //&& b.inv2() // Cut recursion
    )
  }

  twostate lemma adm() requires goodPreAndLegalChanges() ensures inv2() && inv() {}

  constructor (ghost universe: Universe, b: B)
    requires universe.globalInv() && universe == b.universe && b.inv() && !b.valid
    modifies universe, b
    ensures this.baseInv() && universe.globalInv()
  {
    this.universe := universe;
    this.b := b;
    new;
    join();
    this.b.a := this;
    this.valid := true;
    this.b.valid := true;
    universe.lci();
  }
}

class B extends Object {
  ghost var valid: bool // Like in VCC
  ghost var a: A

  ghost predicate inv() reads * {
    && localInv()
    && (valid ==> a.inv())
  }
  ghost predicate localInv() reads * {
    && baseInv()
    && universe == a.universe
    && (valid ==>
      && a.valid
      && a.b == this
      //&& a.inv() // Cut recursion
    )
  }
  
  twostate predicate inv2() reads * {
    && localInv2()
    && (old(valid) ==> a.inv2())
  }
  twostate predicate localInv2() reads * {
    && (old(valid) ==>
      && valid // This makes deallocation impossible
      && old(a) == a
      //&& a.inv2() // Cut recursion
    )
  }

  twostate lemma adm() requires goodPreAndLegalChanges() ensures inv2() && inv() {}

  constructor (ghost universe: Universe, a: A)
    requires universe.globalInv() && universe == a.universe && a.inv() && !a.valid
    modifies universe, a
    ensures this.baseInv() && universe.globalInv()
  {   
    this.universe := universe;
    this.a := a;
    new;
    join();
    this.a.b := this;
    this.valid := true;
    this.a.valid := true;
    universe.lci();
  }
}
