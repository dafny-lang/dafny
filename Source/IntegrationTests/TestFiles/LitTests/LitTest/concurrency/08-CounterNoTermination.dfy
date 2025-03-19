// RUN: %testDafnyForEachResolver "%s"


// This program shows how to model a program that concurrently increments a counter by a fixed amount.
// This encoding requires the user to provide an invariant for each program point.
//
// Rust-like source code:
// fn incrementer(counter: Arc<AtomicIsize>, remaining: AtomicIsize)
//   requires remaining.data == 10
//   ensures remaining.data == 0
// {
//   let mut i = 0;
//   while i < 10 {
//     let initial_value = counter.load(SeqCst);
//     counter.fetch_add(1, SeqCst);
//     let final_value = counter.load(SeqCst);
//     assert!(final_value >= initial_value + 1);
//     i += 1;
//     remaining.fetch_sub(1, SeqCst);
//   }
//   assert!(i == 10);
// }

// A universe of objects playing under LCI rules
trait Universe extends object {
  // The set of objects in the universe
  ghost var content: set<Object>

  // Universe invariant: the universe doesn't contain itself,
  // and its objects in this universe agree that they are in this universe.
  // We define this to allow a generic object operation (O.join below) to add the object to the universe,
  // without having to check the object invariants.
  ghost predicate globalBaseInv() reads this, content {
    forall o: Object | o in content :: && o.universe == this && o as object != this
  }

  // Global 1-state invariant: all objects satisfy their individual invariants.
  ghost predicate globalInv() reads * {
    globalBaseInv() && (forall o: Object | o in content :: o.inv())
  }

  // Global 2-state invariant: all old objects satisfy their 2-state invariants.
  twostate predicate globalInv2() reads * {
    && (forall o: Object | o in old(content) :: o in content && o.inv2())
  }

  twostate predicate legalTransition(running: set<Thread>) reads * { // Transitive by construction
    && old(globalInv())
    && globalBaseInv()
    && old(content) <= content
    // The first condition for legality: old objects that change a field must obey their 1- and 2-state invariants.
    && (forall o: Object | o in old(content) :: unchanged(o) || (o.inv() && o.inv2()))
    // The second condition for legality: new objects must satisfy their invariants.
    && (forall o: Object | o in content && o !in old(content) :: o.inv())
    // Version numbers only increase
    && (forall o: OwnedObject | o in old(content):: old(o.nonvolatileVersion) <= o.nonvolatileVersion)
    // Objects cannot change the nonvolatile fields if they are directly owned by threads that are not running.
    // The 2-state invariant of OwnedObject extends this property to objects that are transitively owned by the threads.
    && (forall t: Thread | t in running :: t.universe == this && t in old(content))
    && (forall o: OwnedObject | o in old(content) && old(o.owner) is Thread :: old(o.owner) as Thread !in running ==> old(o.nonvolatileVersion) == o.nonvolatileVersion)
  }

  // Helper
  twostate lemma proveUnchangedNonvolatileFields()
    ensures forall o: OwnedObject | o in old(content) && unchanged(o) :: o.unchangedNonvolatileFields()
  {
    forall o: OwnedObject | o in old(content) && unchanged(o) ensures o.unchangedNonvolatileFields() {
      o.proveUnchangedNonvolatileFields();
    }
  }

  // LCI soundness: legal transitions are good. This makes use of the admissibility obligations build into Object's.
  // The `TypingAxiom3(running)` lemma is often useful to prove the precondition of this lemma.
  twostate lemma lci(running: Thread)
    requires legalTransition({running})
    ensures globalInv() && globalInv2()
  {
    forall o: Object | o in old(content) && o.goodPreAndLegalChanges(running) ensures o.inv2() && o.inv() { o.admissibility(running); }
  }
}

// A generic object trait
trait Object extends object {
  // Universe of which the Object is a member.
  // This should really be a constant, but I don't know how to do that while factoring out join below,
  // because traits can't have constructors.
  const universe: Universe
  
  // Base invariant: we're in the universe, and the universe satisfies its base.
  ghost predicate baseInv() reads * { this in universe.content && universe.globalBaseInv() }

  // Join the universe
  ghost method join()
    requires universe.globalBaseInv() && this as object != universe
    modifies universe
    ensures baseInv() && universe.content == old(universe.content) + { this }
    ensures unchanged(universe.content) // This method doesn't modify fields of objects in the universe
  {
    universe.content := universe.content + { this };
  }

  // Precondition for the admissibility check.
  // This is broken into a separate predicate because Dafny currently doesn't allow adm.requires() in a 1-state context
  twostate predicate goodPreAndLegalChanges(running: Thread) reads * {
    && old(baseInv() && universe.globalInv())
    && baseInv()
    && unchanged(this)
    && universe.legalTransition({running})
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
  ghost predicate isOwnedObject()
}

trait NonOwnedObject extends Object {
  // To prevent a class from extending both OwnedObject and NonOwnedObject
  ghost predicate isOwnedObject() { false }
}

class Thread extends NonOwnedObject {
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
    new;
    TypingAxiom3(this);
    join();
    universe.proveUnchangedNonvolatileFields();
    universe.lci(running);
  }
}

trait OwnedObject extends Object {
  ghost var nonvolatileVersion: int
  ghost var owner: Object // nonvolatile

  ghost predicate localInv() reads * {
    && baseInv()
    && owner.universe == universe && owner in universe.content
    && baseUserInv()
    && localUserInv()
  }
  ghost predicate inv() reads * ensures inv() ==> localInv() {
    && localInv()
    && userInv()
  }

  twostate predicate localInv2() reads * {
    && localUserInv2()
    && (old(nonvolatileVersion) == nonvolatileVersion ==>
      // Nonvolatile fields are only allowed to change when the nonvolatileVersion changes.
      // (The proveUnchangedNonvolatileFields lemma should be useful to prove this.)
      && unchangedNonvolatileFields()
      // Transitivity: if a nonvolatileVersion doesn't change, the same should apply to all owned objects
      && (forall o: OwnedObject | o in old(universe.content) && old(o.owner) == this :: old(o.nonvolatileVersion) == o.nonvolatileVersion)
    )
    && (old(owner) is OwnedObject ==>
      var oldOwner := old(owner) as OwnedObject;
      // The nonvolatileVersion cannot change if the version of the old owner doesn't change.
      old(oldOwner.nonvolatileVersion) == oldOwner.nonvolatileVersion ==> old(nonvolatileVersion) == nonvolatileVersion
    )
  }
  twostate predicate inv2() reads * ensures inv2() ==> localInv2() {
    && localInv2()
    && userInv2()
    // When the owner changes, the invariant of the old and new owner must hold.
    && (old(owner) != owner ==>
      && old(owner).localInv()
      && old(owner).localInv2()
      && owner.localInv()
      // In case the new owner existed in the old state
      && (var currOwner := owner; old(allocated(currOwner)) ==> owner.localInv2())
    )
  }

  // To prevent a class from extending both OwnedObject and NonOwnedObject
  ghost predicate isOwnedObject() { true }

  twostate predicate unchangedNonvolatileFields() reads this {
    old(owner) == owner && unchangedNonvolatileUserFields()
  }
  twostate lemma proveUnchangedNonvolatileFields() requires unchanged(this) ensures unchangedNonvolatileFields() {
    proveUnchangedNonvolatileUserFields();
  }

  twostate predicate unchangedNonvolatileUserFields() reads this // Checking transitivity is up to the classes that implement this trait. See EmptyType for an example of how to check transitivity.
  twostate lemma proveUnchangedNonvolatileUserFields() requires unchanged(this) ensures unchangedNonvolatileUserFields()

  ghost predicate baseUserInv() reads *
  ghost predicate localUserInv() reads *
  twostate predicate localUserInv2() reads *
  ghost predicate userInv() reads * ensures userInv() ==> localUserInv()
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2()
}

method BumpVersion(ghost last: int) returns (res: int) ensures res > last

// Axioms: Instances of OwnedObject cannot alias instances of NonOwnedObjects.
// This is to workaround an incompleteness of Dafny, which doesn't know that classes don't alias instances of traits that the class doesn't extend.
// I asked on Slack if there is a way to assume these globally.
lemma TypingAxiom1(universe: Universe)
  ensures forall a: NonOwnedObject, b: OwnedObject | a in universe.content && b in universe.content :: a as Object != b
lemma TypingAxiom2(universe: Universe, a: NonOwnedObject)
  ensures forall b: OwnedObject | b in universe.content :: a as object != b
lemma TypingAxiom3(a: NonOwnedObject)
  ensures !((a as Object) is OwnedObject)
lemma TypingAxiom4(b: OwnedObject)
  ensures !((b as Object) is NonOwnedObject)

// An example of type without fields
class EmptyType extends OwnedObject {
  twostate predicate unchangedNonvolatileUserFields() reads this {
    true
  }
  twostate lemma proveUnchangedNonvolatileUserFields() requires unchanged(this) ensures unchangedNonvolatileUserFields() {}

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
    ensures objectGlobalInv() && universe.globalInv2()
    ensures this.universe == universe && this.owner == running
    ensures universe.content == old(universe.content) + { this }
  {
    this.universe := universe;
    this.owner := running;
    new;
    join();
    universe.proveUnchangedNonvolatileFields();
    TypingAxiom3(running);
    universe.lci(running);
  }
}

// A strictly increasing counter
class AtomicCounter extends OwnedObject {
  var value: int // volatile

  twostate predicate unchangedNonvolatileUserFields() reads this {
    true
  }
  twostate lemma proveUnchangedNonvolatileUserFields() requires unchanged(this) ensures unchangedNonvolatileUserFields() {}

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
    old(value) <= value
  }
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2() {
    && localUserInv2()
  }

  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {}

  constructor(universe: Universe, ghost running: Thread, initialValue: int)
    requires universe.globalInv() && running.universe == universe && running.inv()
    modifies universe
    ensures objectGlobalInv() && universe.globalInv2()
    ensures this.universe == universe && this.owner == running && this.value == initialValue
    ensures universe.content == old(universe.content) + { this }
  {
    this.universe := universe;
    this.value := initialValue;
    this.owner := running;
    new;
    join();
    universe.proveUnchangedNonvolatileFields();
    TypingAxiom3(running);
    universe.lci(running);
  }
}

class Remaining extends OwnedObject {
  var value: int // nonvolatile

  twostate predicate unchangedNonvolatileUserFields() reads this {
    && old(value) == value
  }
  twostate lemma proveUnchangedNonvolatileUserFields() requires unchanged(this) ensures unchangedNonvolatileUserFields() {}

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

  constructor(universe: Universe, ghost running: Thread, initialValue: int)
    requires universe.globalInv() && running.universe == universe && running.inv()
    modifies universe
    ensures objectGlobalInv() && universe.globalInv2()
    ensures this.universe == universe && this.owner == running && this.value == initialValue
    ensures universe.content == old(universe.content) + { this }
  {
    this.universe := universe;
    this.value := initialValue;
    this.owner := running;
    new;
    join();
    universe.proveUnchangedNonvolatileFields();
    TypingAxiom3(running);
    universe.lci(running);
  }
}

// Rust-like source code:
// fn incrementer(counter: Arc<AtomicIsize>, remaining: AtomicIsize)
//   requires remaining.data == 10
//   ensures remaining.data == 0
// {
//            // 0: inv_pre: remaining.data == 10
//   let mut i = 0;
//            // 1: inv_pre: 0 <= i <= 10 && remaining.data == 10
//   while i < 10 {
//            // 2: inv_pre: 0 <= i <= 9 && remaining.data + i == 10
//     let initial_value = counter.load(SeqCst);
//            // 3: inv_pre: 0 <= i <= 9 && initial_value <= counter.data && remaining.data + i == 10
//     counter.fetch_add(1, SeqCst);
//            // 4: inv_pre: 0 <= i <= 9 && initial_value + 1 <= counter.data && remaining.data + i == 10
//     let final_value = counter.load(SeqCst);
//            // 5: inv_pre: 0 <= i <= 9 && initial_value + 1 <= final_value <= counter.data && remaining.data + i == 10
//     assert!(final_value >= initial_value + 1);
//            // 6: inv_pre: 0 <= i <= 9 && remaining.data + i == 10
//     i += 1;
//            // 7: inv_pre: 0 <= i <= 10 && remaining.data + i == 11
//     remaining.fetch_sub(1, SeqCst);
//            // 8: inv_pre: 0 <= i <= 10 && remaining.data + i == 10
//   }
//            // 9: (after loop) inv_pre: i == 10 && remaining.data == 0
//   assert!(i == 10);
//            // 10: remaining.data == 0
//   (check postcondition)
// }

class IncrementerMethod extends OwnedObject {
  var programCounter: int
  var counter: AtomicCounter
  var remaining: Remaining
  var initial_value: int
  var final_value: int
  var i: int

  twostate predicate unchangedNonvolatileUserFields() reads this {
    && old(programCounter) == programCounter
    && old(counter) == counter
    && old(remaining) == remaining
    && old(initial_value) == initial_value
    && old(final_value) == final_value
    && old(i) == i
  }
  twostate lemma proveUnchangedNonvolatileUserFields() requires unchanged(this) ensures unchangedNonvolatileUserFields() {}

  ghost predicate baseUserInv() reads * {
    && counter in universe.content && counter.universe == universe
    && remaining in universe.content && remaining.universe == universe
  }

  ghost predicate localUserInv() reads * {
    && remaining.owner == this
    && 0 <= programCounter <= 10
    && (programCounter ==  0 ==> remaining.value == 10)
    && (programCounter ==  1 ==> remaining.value == 10     && i == 0)
    && (programCounter ==  2 ==> remaining.value + i == 10 && 0 <= i <= 9)
    && (programCounter ==  3 ==> remaining.value + i == 10 && 0 <= i <= 9 && initial_value <= counter.value)
    && (programCounter ==  4 ==> remaining.value + i == 10 && 0 <= i <= 9 && initial_value + 1 <= counter.value)
    && (programCounter ==  5 ==> remaining.value + i == 10 && 0 <= i <= 9 && initial_value + 1 <= final_value <= counter.value)
    && (programCounter ==  6 ==> remaining.value + i == 10 && 0 <= i <= 9)
    && (programCounter ==  7 ==> remaining.value + i == 11 && 0 <= i <= 10)
    && (programCounter ==  8 ==> remaining.value + i == 10 && 0 <= i <= 10)
    && (programCounter ==  9 ==> remaining.value == 0      && i == 10)
    && (programCounter == 10 ==> remaining.value == 0)
  }
  ghost predicate userInv() reads * ensures userInv() ==> localUserInv() {
    && localUserInv()
    && counter.localInv()
    && remaining.localInv()
  }

  twostate predicate localUserInv2() reads * {
    && old(owner) == owner
    && old(counter) == counter
    && old(remaining) == remaining
    && (old(programCounter) == 2 && programCounter == 3 ==> old(i) == i)
    && (old(programCounter) == 3 && programCounter == 4 ==> old(i) == i)
    && (old(programCounter) == 4 && programCounter == 5 ==> old(i) == i)
    && (old(programCounter) == 5 && programCounter == 6 ==> old(i) == i)
    && (old(programCounter) == 6 && programCounter == 7 ==> old(i) < i)
    && (old(programCounter) == 7 && programCounter == 8 ==> old(i) == i)
    && (old(programCounter) == 8 && programCounter == 2 ==> old(i) == i)
    && (old(programCounter) == 8 && programCounter == 9 ==> old(i) == i)
  }
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2() {
    && localUserInv2()
    && counter.localInv2()
    && remaining.localInv2()
  }

  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {}

  constructor(universe: Universe, ghost running: Thread, counter: AtomicCounter, remaining: Remaining)
    requires universe.globalInv() && running.universe == universe && running.inv() && counter.universe == universe && counter.inv() && remaining.universe == universe && remaining.inv()
    requires remaining.owner == running && remaining.value == 10 // The precondition
    modifies universe, remaining
    ensures objectGlobalInv() && universe.globalInv2()
    ensures this.universe == universe && this.counter == counter && this.remaining == remaining && this.remaining.owner == this && this.programCounter == 0 && this.owner == running
    ensures universe.content == old(universe.content) + { this }
  {
    this.universe := universe;
    this.programCounter := 0;
    this.counter := counter;
    this.remaining := remaining;
    this.owner := running;
    new;
    join();
    remaining.owner := this;
    remaining.nonvolatileVersion := BumpVersion(remaining.nonvolatileVersion);
    universe.proveUnchangedNonvolatileFields();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement0(ghost running: Thread)
    requires this.objectGlobalInv() && running.universe == universe && running in universe.content && this.owner == running && programCounter == 0
    modifies this
    ensures this.objectGlobalInv() && universe.globalInv2() && programCounter == 1
  {
    i := 0;
    programCounter := 1;
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.proveUnchangedNonvolatileFields();
    TypingAxiom3(running);
    universe.lci(running);
  }
  
  method Statement1(ghost running: Thread)
    requires this.objectGlobalInv() && running.universe == universe && running in universe.content && this.owner == running && programCounter == 1
    modifies this
    ensures this.objectGlobalInv() && universe.globalInv2() && (programCounter == 2 || programCounter == 9)
  {
    if (i < 10) { programCounter := 2; } else { programCounter := 9; }
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.proveUnchangedNonvolatileFields();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement2(ghost running: Thread)
    requires this.objectGlobalInv() && running.universe == universe && running in universe.content && this.owner == running && programCounter == 2
    modifies this
    ensures this.objectGlobalInv() && universe.globalInv2() && programCounter == 3
  {
    initial_value := counter.value;
    programCounter := 3;
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.proveUnchangedNonvolatileFields();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement3(ghost running: Thread)
    requires this.objectGlobalInv() && running.universe == universe && running in universe.content && this.owner == running && programCounter == 3
    modifies this, counter
    ensures this.objectGlobalInv() && universe.globalInv2() && programCounter == 4
  {
    counter.value := counter.value + 1;
    programCounter := 4;
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.proveUnchangedNonvolatileFields();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement4(ghost running: Thread)
    requires this.objectGlobalInv() && running.universe == universe && running in universe.content && this.owner == running && programCounter == 4
    modifies this
    ensures this.objectGlobalInv() && universe.globalInv2() && programCounter == 5
  {
    final_value := counter.value;
    programCounter := 5;
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.proveUnchangedNonvolatileFields();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement5(ghost running: Thread)
    requires this.objectGlobalInv() && running.universe == universe && running in universe.content && this.owner == running && programCounter == 5
    modifies this
    ensures this.objectGlobalInv() && universe.globalInv2() && programCounter == 6
  {
    assert initial_value + 1 <= final_value;
    programCounter := 6;
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.proveUnchangedNonvolatileFields();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement6(ghost running: Thread)
    requires this.objectGlobalInv() && running.universe == universe && running in universe.content && this.owner == running && programCounter == 6
    modifies this
    ensures this.objectGlobalInv() && universe.globalInv2() && programCounter == 7
  {
    i := i + 1;
    programCounter := 7;
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.proveUnchangedNonvolatileFields();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement7(ghost running: Thread)
    requires this.objectGlobalInv() && running.universe == universe && running in universe.content && this.owner == running && programCounter == 7
    modifies this, remaining
    ensures this.objectGlobalInv() && universe.globalInv2() && programCounter == 8
  {
    remaining.value := remaining.value - 1;
    remaining.nonvolatileVersion := BumpVersion(remaining.nonvolatileVersion);
    programCounter := 8;
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.proveUnchangedNonvolatileFields();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement8(ghost running: Thread)
    requires this.objectGlobalInv() && running.universe == universe && running in universe.content && this.owner == running && programCounter == 8
    modifies this
    ensures this.objectGlobalInv() && universe.globalInv2() && (programCounter == 2 || programCounter == 9)
  {
    if (i < 10) { programCounter := 2; } else { programCounter := 9; }
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.proveUnchangedNonvolatileFields();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement9(ghost running: Thread)
    requires this.objectGlobalInv() && running.universe == universe && running in universe.content && this.owner == running && programCounter == 9
    modifies this
    ensures this.objectGlobalInv() && universe.globalInv2() && programCounter == 10
  {
    assert i == 10;
    programCounter := 10;
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.proveUnchangedNonvolatileFields();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement10(ghost running: Thread)
    requires this.objectGlobalInv() && running.universe == universe && running in universe.content && this.owner == running && programCounter == 10
    ensures this.objectGlobalInv() && universe.globalInv2() && programCounter == 10
  {
    assert remaining.value == 0;
    universe.proveUnchangedNonvolatileFields();
    TypingAxiom3(running);
    universe.lci(running);
  }
}
