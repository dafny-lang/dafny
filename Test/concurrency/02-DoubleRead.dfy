// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This program shows how to model a program that reads twice from a shared non-decreasing counter.
// This encoding requires the user to provide an invariant for each program point.
//
// Rust-life source code:
// fn worker(counter: Arc<AtomicIsize>) {
//   let initial_value = counter.load(SeqCst);
//   let final_value = counter.load(SeqCst);
//   assert!(final_value >= initial_value);
// }

// Cast a trait type to an object type.
// Dafny doesn't allow to do reference equality between a trait and an object type, so we use this function to upcast where needed.
function upCast(o: object): object {o}

// A universe of objects playing under LCI rules 
trait Universe {
  // The set of objects in the universe
  ghost var content: set<Object>

  // Universe invariant: the universe doesn't contain itself, 
  // and its objects in this universe agree that they are in this universe.
  // We define this to allow a generic object operation (O.join below) to add the object to the universe, 
  // without having to check the object invariants.
  predicate i0() reads this, content {
    forall o: Object | o in content :: o.universe == this && upCast(o) != this
  }
  
  // Global 1-state invariant: all objects satisfy their individual invariants.
  predicate i() reads * {
    i0() && forall o: Object | o in content :: o.i()
  }
  
  // Global 2-state invariant: all old objects satisfy their 2-state invariants.
  twostate predicate i2() reads * {
    forall o: Object | o in old(content) :: o in content && o.i2()
  }
  
  // The first condition for legality: old objects that change a field must obey their 1- and 2-state invariants.
  twostate predicate legal0() reads * {
    forall o: Object | o in old(content) :: unchanged(o) || (o.i2() && o.i())
  }
  
  // The second condition for legality: new objects must satisfy their invariants.
  twostate predicate legal1() reads * {
    forall o: Object | o in content && o !in old(content) :: o.i()
  }
  
  // A legal transition is one that starts from a good state, preserves the universe invariant, and meets the legality conditions. 
  twostate predicate legal() reads * {
    old(i()) && i0() && old(content) <= content && legal0() && legal1()
  }
  
  // LCI soundness: legal transitions are good. This makes use of the admissibility obligations build into Object's.
  twostate lemma lci()
    requires legal()
    ensures i() && i2()
  {
    forall o: Object | o in old(content) && o.admPre() ensures o.i2() && o.i() { o.adm(); }
  }
}

// A generic object trait
trait Object {
  // Universe of which the Object is a member.
  // This should really be a constant, but I don't know how to do that while factoring out join below,
  // because traits can't have constructors.
  ghost const universe: Universe

  // Base invariant: we're in the universe, and the universe satisfies its base.
  predicate i0() reads * { this in universe.content && universe.i0() }
  
  // Join the universe
  ghost method join()
    requires universe.i0() && upCast(this) != universe
    modifies universe 
    ensures i0() && universe.content == old(universe.content) + { this }
  {
    universe.content := universe.content + { this }; 
  }

  // Precondition for the admissibility check.
  // This is broken into a separate predicate because Dafny currently doesn't allow adm.requires() in a 1-state context
  twostate predicate admPre() reads * { i0() && old(i0() && universe.i()) && unchanged(this) && universe.legal() }

  // Global invariant (from o's perspective) - I am in the universe and the universe is good. (This implies I am good also.)
  predicate gi() reads * { i0() && universe.i() }

  // Global 2-state invariant (from o's perspective).
  twostate predicate gi2() requires old(gi()) reads * { i0() && universe.i2() }

  // To be implemented in the class: 1-state invariant, 2-state invariant, and admissibility proof.
  predicate i() reads * // what is the * here?
  twostate predicate i2() reads *
  twostate lemma adm() requires admPre() ensures i2() && i()
}

// Arc<AtomicIsize>
class ArcAtomicIsize extends Object {
  var data: int

  // Invariant
  predicate i() reads * {
    // Base invariant holds: Instances of this type are in the universe and they all have a reference to the universe.
    && i0()
  }
  twostate predicate i2() reads * {
    && old(data) <= data
  }

  // Admissibility proof
  twostate lemma adm() {}

  constructor (ghost universe: Universe, initial_data: int)
    requires universe.i()
    modifies universe
    ensures universe.i()
  {
    this.universe := universe;
    data := initial_data;
    // End of initialization phase, during which usages of `this` are restricted.
    new;
    // Add this object to the universe
    join();
    // Use LCI to prove that we don't break other object invariants
    universe.lci();
  }
}

// fn worker(counter: Arc<AtomicIsize>) {
//   let initial_value = counter.load(SeqCst); // 1
//   let final_value = counter.load(SeqCst);   // 2
//   assert!(final_value >= initial_value);    // 3
// }                                           // 4

class WorkerMethod extends Object {
  var next_stmt: int // The next statement that should be executed.

  // A field for every argument and local variable of the source method.
  var counter: ArcAtomicIsize
  var initial_value: int
  var final_value: int

  predicate i() reads * {
    && i0()
    && 1 <= next_stmt <= 4
    && universe == counter.universe
    && counter.i()
    && (next_stmt > 1 ==> initial_value <= counter.data)
    && (next_stmt > 2 ==> initial_value <= final_value <= counter.data)
  }
  twostate predicate i2() reads * {
    && counter == old(counter)
    && counter.i2()
    && old(next_stmt) <= next_stmt
  }

  twostate lemma adm() requires admPre() ensures i2() && i() {}

  constructor (ghost universe: Universe, counter: ArcAtomicIsize)
    requires universe.i() && universe == counter.universe && counter.i()
    modifies universe
    ensures this.i() && universe.i()
  {   
    this.universe := universe;
    this.next_stmt := 1;
    this.counter := counter;
    new;
    join();
    universe.lci();
  }

  method Statement1()
    requires gi() && next_stmt == 1
    modifies this
    ensures gi2()
  {
    initial_value := counter.data;
    next_stmt := next_stmt + 1;
    universe.lci();
  }

  method Statement2()
    requires gi() && next_stmt == 2
    modifies this
    ensures gi2()
  {
    final_value := counter.data;
    next_stmt := next_stmt + 1;
    universe.lci();
  }

  method Statement3()
    requires gi() && next_stmt == 3
    modifies this
    ensures gi2()
  {
    // Check the Rust assertion. This can also be seen as a check that the `assert!(..)` doesn't panic.
    assert initial_value <= final_value;
    next_stmt := next_stmt + 1;
    universe.lci();
  }

  method Statement4()
    requires gi() && next_stmt == 4
    modifies this
    ensures gi2()
  {
    // Check the postcondition of the method. In this case, `true`.
    assert true;
    universe.lci();
  }
}
