// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This program shows how to encode ownership and the property that objects owned by a thread that doesn't execute don't change.

// A universe of objects playing under LCI rules
trait Universe {
  // The set of objects in the universe
  ghost var content: set<Object>

  // Universe invariant: the universe doesn't contain itself,
  // and its objects in this universe agree that they are in this universe.
  // We define this to allow a generic object operation (O.join below) to add the object to the universe,
  // without having to check the object invariants.
  ghost predicate globalBaseInv() reads this, content {
    && (forall o: Object | o in content :: && o.universe == this && o as object != this)
    && (forall o: OwnedObject | o in content :: o.owner in content && (!o.closed ==> o.owner is Thread))
  }

  // Global 1-state invariant: all objects satisfy their individual invariants.
  ghost predicate globalInv() reads * {
    && globalBaseInv()
    && (forall o: Object | o in content :: o.inv())
  }

  // Global 2-state invariant: all old objects satisfy their 2-state invariants.
  twostate predicate globalInv2() reads * {
    forall o: Object | o in old(content) :: o in content && o.inv2()
  }

  // A legal transition is one that starts from a good state, preserves the universe invariant, and meets the legality conditions.
  twostate predicate multipleLegalTransitions(running: set<Thread>) reads * { // Transitive by construction
    && old(globalInv())
    && globalBaseInv()
    && old(content) <= content
    && (forall o: Object | o !in old(content) && o in content :: !old(allocated(o)))
    // The first condition for legality: old objects that change a field must obey their 1- and 2-state invariants.
    && (forall o: Object | o in old(content) :: unchanged(o) || o.inv())
    // The second condition for legality: new objects must satisfy their invariants.
    && (forall o: Object | o in content && o !in old(content) :: o.inv())
    // Objects owned by threads that are not running don't change.
    && (forall t: Thread | t in running :: t.universe == this && t in old(content))
    && (forall o: OwnedObject | o in old(content) && old(o.owner) is Thread :: old(o.owner) as Thread !in running ==> unchanged(o))
  }
  twostate predicate legalTransition(running: Thread) reads * {
    && multipleLegalTransitions({running})
    // The first condition for legality: old objects that change a field must obey their 1- and 2-state invariants.
    && (forall o: Object | o in old(content) :: unchanged(o) || o.inv2())
  }

  // LCI soundness: legal transitions are good. This makes use of the admissibility obligations build into Object's.
  twostate lemma lci(running: Thread)
    requires legalTransition(running)
    ensures globalInv() && globalInv2()
  {
    forall o: Object | o in old(content) && o.goodPreAndLegalChanges(running) ensures o.inv2() && o.inv() { o.admissibility(running); }
  }

  // Model the preemption of a given thread. Any other thread will have a chance to execute any number of legal transitions,
  // perturbating objects in the universe that are not owned by the preempting thread.
  method Preemption(ghost preempting: Thread)
    requires preempting.universe == this && preempting.objectGlobalInv()
    modifies this, this.content, preempting
    ensures preempting.universe == this && preempting.objectGlobalInv()
    //ensures globalInv2() // No, because it's not guaranteed to be transitive
    ensures multipleLegalTransitions(set t: Thread | t in old(content) && t != preempting) // Other threads executed any number of legal transitions
  {
    // Do nothing. Just havock stuff on the caller side.
  }
}

// A generic object trait
trait Object {
  // Universe of which the Object is a member.
  // This should really be a constant, but I don't know how to do that while factoring out join below,
  // because traits can't have constructors.
  const universe: Universe
  
  // Base invariant: we're in the universe, and the universe satisfies its base.
  ghost predicate baseInv() reads * { this in universe.content && universe.globalBaseInv() }

  // Join the universe
  ghost method join()
    requires universe.globalBaseInv() && this as object != universe
    requires this is OwnedObject ==> (
      var o := this as OwnedObject;
      && o.owner in universe.content
      && (!o.closed ==> o.owner is Thread)
    )
    modifies universe
    ensures baseInv() && universe.content == old(universe.content) + { this }
    ensures unchanged(universe.content) // This method doesnt modify fields of objects in the universe
  {
    universe.content := universe.content + { this };
  }

  // Precondition for the admissibility check.
  // This is broken into a separate predicate because Dafny currently doesn't allow adm.requires() in a 1-state context
  twostate predicate goodPreAndLegalChanges(running: Thread) reads * {
    && old(baseInv() && universe.globalInv())
    && baseInv()
    && unchanged(this)
    && universe.legalTransition(running)
  }

  // Global invariant (from o's perspective) - I am in the universe and the universe is good. (This implies I am good also.)
  ghost predicate objectGlobalInv() reads * { baseInv() && universe.globalInv() }

  // Global 2-state invariant (from o's perspective).
  twostate predicate objectGlobalInv2() requires old(objectGlobalInv()) reads * { baseInv() && universe.globalInv2() }

  // To be implemented in the class: 1-state invariant, 2-state invariant, and admissibility proof.
  ghost predicate localInv() reads *
  twostate predicate localInv2() reads *
  ghost predicate inv() ensures inv() ==> localInv() reads *
  twostate predicate inv2() ensures inv2() ==> localInv2() reads *
  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv()
  
  // To prevent a class from extending both OwnedObject and NonOwnedObject
  ghost predicate instanceOfOwnedObject()
}

trait NonOwnedObject extends Object {
  // To prevent a class from extending both OwnedObject and NonOwnedObject
  ghost predicate instanceOfOwnedObject() { false }
}

trait OwnedObject extends Object {
  ghost var owner: Object
  ghost var closed: bool

  ghost predicate localInv() reads * {
    && baseInv()
    && owner.universe == universe && owner in universe.content
    && baseUserInv()
    && (closed ==> localUserInv())
  }
  ghost predicate inv() reads * ensures inv() ==> localInv() {
    && localInv()
    && (closed ==> userInv())
  }

  twostate predicate localInv2() reads * {
    && (old(closed) && closed ==> localUserInv2())
  }
  twostate predicate inv2() reads * ensures inv2() ==> localInv2() {
    var currOwner := owner;
    && localInv2()
    && userInv2()
    // From the LCI paper
    && (!old(closed) || !closed ==>
      userFieldsUnchanged() || (
        && (old(allocated(currOwner)) ==> currOwner.localInv2())
      )
    )
    // when wrapping or unwrapping
    && (old(closed) != closed ==>
      && old(owner) == owner
      //&& owner == universe.runningThread // FIXME: cannot be expressed in an invariant
      && owner.localInv2()
    )
    // when wrapping, we move ownership of the fields from the thread to the object
    && (!old(closed) && closed ==>
      //&& old(userFieldsOwnedBy(universe.runningThread)) // FIXME: cannot be expressed in an invariant
      && userFieldsOwnedBy(this)
    )
    // when unwrapping, we move ownership of the fields from the object to the thread
    && (old(closed) && !closed ==>
      && old(userFieldsOwnedBy(this))
      //&& userFieldsOwnedBy(universe.runningThread) // FIXME: cannot be expressed in an invariant
    )
    // when the owner changes, the invariant of both the old and the new owner must hold
    && (old(owner) != owner ==>
      && old(owner).localInv2()
      && old(owner).localInv() // Necessary to verify the admissibility of the Thread class
      && (old(allocated(currOwner)) ==> currOwner.localInv2())
      && owner.localInv() // Necessary to verify the admissibility of the Thread class
    )
  }

  // To prevent a class from extending both OwnedObject and NonOwnedObject
  ghost predicate instanceOfOwnedObject() { true }

  ghost predicate userFieldsOwnedBy(owner: Object) reads *
  twostate predicate userFieldsUnchanged() reads *

  ghost predicate baseUserInv() reads *
  ghost predicate localUserInv() reads *
  twostate predicate localUserInv2() reads *
  ghost predicate userInv() reads * ensures userInv() ==> localUserInv()
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2()
}

// Axioms: Instances of OwnedObject cannot alias instances of NonOwnedObjects.
// This is to workaround an incompleteness of Dafny, which doesn't know that classes don't alias instances of traits that the class doesn't extend.
lemma TypingAxiom1(universe: Universe)
  ensures forall a: NonOwnedObject, b: OwnedObject | a in universe.content && b in universe.content :: a as Object != b
lemma TypingAxiom2(universe: Universe, a: NonOwnedObject)
  ensures forall b: OwnedObject | b in universe.content :: a as object != b
lemma TypingAxiom3(a: NonOwnedObject)
  ensures !((a as Object) is OwnedObject)
lemma TypingAxiom4(b: OwnedObject)
  ensures !((b as Object) is NonOwnedObject)

class Thread extends NonOwnedObject {
  // ghost var ownedObjects: set<OwnedObject> // It seems useless

  ghost predicate localInv() reads * {
    && baseInv()
  }
  ghost predicate inv() reads * ensures inv() ==> localInv() {
    && localInv()
  }

  twostate predicate localInv2() reads * {
    true
  }
  twostate predicate inv2() reads * ensures inv2() ==> localInv2() {
    localInv2()
  }

  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {}

  // Here we require a thread to create a thread. Programs shold assume that an initial thread exists in the universe.
  constructor(universe: Universe, ghost running: Thread)
    requires universe.globalInv() && running.universe == universe && running.inv()
    modifies universe
    ensures objectGlobalInv() && universe.globalInv2()
  {
    this.universe := universe;
    //this.ownedObjects := {};
    new;
    TypingAxiom3(this);
    join();
    universe.lci(running);
  }
}

// An example of type without fields
class EmptyType extends OwnedObject {
  ghost predicate userFieldsOwnedBy(owner: Object) reads * {
    true
  }
  twostate predicate userFieldsUnchanged() reads * {
    true
  }
  
  ghost predicate baseUserInv() reads * {
    && true
  }

  ghost predicate localUserInv() reads * {
    && true
  }
  ghost predicate userInv() reads * ensures userInv() ==> localUserInv() {
    && localUserInv()
  }

  twostate predicate localUserInv2() reads * {
    && true
  }
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2() {
    && localUserInv2()
  }

  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {}

  constructor(universe: Universe, ghost running: Thread)
    requires universe.globalInv() && running.universe == universe && running.inv()
    modifies universe
    //modifies running
    ensures objectGlobalInv() && universe.globalInv2()
    // The following might not always be needed
    ensures this.universe == universe && this.owner == running && this.closed == false
    //ensures running.ownedObjects == old(running.ownedObjects) + { this }
    ensures universe.content == old(universe.content) + { this }
  {
    this.universe := universe;
    this.owner := running;
    this.closed := false;
    new;
    join();
    //running.ownedObjects := running.ownedObjects + { this };
    TypingAxiom1(universe);
    universe.lci(running);
  }
}

// An example of type without fields
class AtomicCounter extends OwnedObject {
  var value: int

  ghost predicate baseUserInv() reads * {
    && true
  }

  ghost predicate userFieldsOwnedBy(owner: Object) reads * {
    true
  }
  twostate predicate userFieldsUnchanged() reads * {
    old(value) == value
  }

  ghost predicate localUserInv() reads * {
    && true
  }
  ghost predicate userInv() reads * ensures userInv() ==> localUserInv() {
    && localUserInv()
  }

  twostate predicate localUserInv2() reads * {
    old(value) <= value
  }
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2() {
    && localUserInv2()
  }

  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {}

  constructor(universe: Universe, ghost running: Thread, initialValue: int)
    requires universe.globalInv() && running.universe == universe && running.inv()
    modifies universe
    //modifies running
    ensures objectGlobalInv() && universe.globalInv2()
    // The following might not always be needed
    ensures this.universe == universe && this.owner == running && this.value == initialValue && this.closed == false 
    //ensures running.ownedObjects == old(running.ownedObjects) + { this }
    ensures universe.content == old(universe.content) + { this }
  {
    this.universe := universe;
    this.owner := running;
    this.closed := false;
    this.value := initialValue;
    new;
    join();
    //running.ownedObjects := running.ownedObjects + { this };
    TypingAxiom1(universe);
    universe.lci(running);
  }
}

// fn double_read(counter: Arc<AtomicIsize>) { // 0: pre state
//   let initial_value = counter.load(SeqCst); // 1: after first statement
//   let final_value = counter.load(SeqCst);   // 2: after second statement
//   assert!(final_value >= initial_value);    // 3: post state, after the last statement
// }                                           // 4: after checking the postcondition

class DoubleReadMethod extends OwnedObject {
  var programCounter: int
  var counter: AtomicCounter
  var initial_value: int
  var final_value: int

  ghost predicate userFieldsOwnedBy(owner: Object) reads * {
    && counter.owner == owner
  }
  twostate predicate userFieldsUnchanged() reads * {
    && old(programCounter) == programCounter
    && old(counter) == counter
    && old(initial_value) == initial_value
    && old(final_value) == final_value
  }
  
  ghost predicate baseUserInv() reads * {
    && counter in universe.content && counter.universe == universe
  }

  ghost predicate localUserInv() reads * {
    // && closed // This is meaningless here
    // && owner == universe.runningThread // Cannot mention the running thread in an invariant
    // && counter.closed // Not admissible
    && counter.owner == this // FIXME: Needed for admissibility because we don't have VCC's handles
    && 0 <= programCounter <= 4
    && (1 <= programCounter ==> initial_value <= counter.value)
    && (2 <= programCounter ==> initial_value <= final_value <= counter.value)
  }
  ghost predicate userInv() reads * ensures userInv() ==> localUserInv() {
    && localUserInv()
  }

  twostate predicate localUserInv2() reads * {
    && old(programCounter) <= programCounter
  }
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2() {
    && localUserInv2()
  }

  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {
  }

  constructor(universe: Universe, ghost running: Thread, counter: AtomicCounter)
    requires universe.globalInv() && running.universe == universe && running.inv() && counter.universe == universe && counter.inv()
    requires counter.owner == running // The running thread should own all parameters
    requires counter.closed // Otherwise we cannot transfer the ownership to this
    modifies universe, counter
    //modifies running
    ensures objectGlobalInv() && universe.globalInv2()
    // The following might not always be needed
    ensures this.universe == universe && this.counter == counter && this.programCounter == 0 && this.owner == running && this.closed == true
    ensures universe.content == old(universe.content) + { this }
    //ensures running.ownedObjects == old(running.ownedObjects) + { this }
  {
    this.universe := universe;
    this.programCounter := 0;
    this.counter := counter;
    this.owner := running;
    this.closed := true;
    new;
    //running.ownedObjects := running.ownedObjects + { this };
    join();
    counter.owner := this;
    TypingAxiom2(universe, running);
    universe.lci(running);
  }

  method Run(ghost running: Thread)
    requires this.objectGlobalInv() && running.universe == universe && running.inv()
    requires programCounter == 0 && closed && this.owner == running // Special requirements of Run
    modifies universe, universe.content, this
  {
    universe.Preemption(running);                              // Interference

    label l0:
    assert universe.globalInv() && programCounter == 0;        // Check that the initial state is good (redundant)
    initial_value := counter.value;                            // Execute the statement
    programCounter := 1;                                       // Update the program counter
    universe.lci@l0(running);
    assert universe.globalInv() && universe.globalInv2@l0();   // Check that the transition is legal

    universe.Preemption(running);                              // Interference

    label l1:
    assert universe.globalInv() && programCounter == 1;        // Check that the initial state is good (redundant)
    final_value := counter.value;                              // Execute the statement
    programCounter := 2;                                       // Update the program counter
    universe.lci@l1(running);
    assert universe.globalInv() && universe.globalInv2@l1();   // Check that the transition is legal

    universe.Preemption(running);                              // Interference

    label l2:
    assert universe.globalInv() && programCounter == 2;        // Check that the initial state is good (redundant)
    assert initial_value <= final_value;                       // Execute the statement
    programCounter := 3;                                       // Update the program counter
    universe.lci@l2(running);
    assert universe.globalInv() && universe.globalInv2@l2();   // Check that the transition is legal

    universe.Preemption(running);                              // Interference

    label l3:
    assert universe.globalInv() && programCounter == 3;        // Check that the initial state is good (redundant)
    assert true;                                               // Check the postcondition
    programCounter := 4;                                       // Update the program counter
    universe.lci@l3(running);                                  // (redundant)
    assert universe.globalInv() && universe.globalInv2@l3();   // Check that the transition is legal (redundant)
  }
}
