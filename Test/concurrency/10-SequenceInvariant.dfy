// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This program shows how to model a program that concurrently increments a counter
// The encoding used using sequential code and claims.

// A universe of objects playing under LCI rules
trait Universe {
  // The set of objects in the universe
  var content: set<Object>

  // Universe invariant: the universe doesn't contain itself,
  // and its objects in this universe agree that they are in this universe.
  // We define this to allow a generic object operation (O.join below) to add the object to the universe,
  // without having to check the object invariants.
  predicate globalBaseInv() reads this, content {
    forall o: Object | o in content :: o.universe == this && o as object != this && o.baseFieldsInv() && o.triggerAxioms()
  }

  // Global 1-state invariant: all objects satisfy their individual invariants.
  predicate globalInv() reads * {
    globalBaseInv() && (forall o: Object | o in content :: o.inv())
  }

  // Global transitive 2-state invariant: all old objects satisfy their transitive 2-state invariants.
  twostate predicate globalSequenceInv2() reads * {
    && forall o: Object | o in old(content) :: o in content && o.sequenceInv2()
  }

  // Global 2-state invariant: all old objects satisfy their 2-state invariants.
  twostate predicate globalInv2() reads * {
    forall o: Object | o in old(content) :: o in content && o.inv2()
  }

  twostate predicate baseLegalTransitionsSequence() reads * {
    && old(globalBaseInv())
    && globalBaseInv()
    // The universe only grows
    && old(content) <= content
    // All objects added to the universe weren't allocated in the old state.
    // This allows to satisfy the modifies clause checks on the caller side in a sequence of methods that might
    // modify the universe. For example, the `Havoc` and `Interference` methods.
    && (forall o: Object | o !in old(content) && o in content :: !old(allocated(o)))
  }

  // This relation describes a sequence of legal transitions, each of which can be performed by a newly created thread
  // or by one of the threads in the `running` parameter.
  // This definition is weaker than `legalTransition`, but it's transitive (if it holds for A->B and B->C then it holds also for A->C).
  // This definition is also monotonic w.r.t. `running`: `legalTransitionsSequence(S)` should imply `legalTransitionsSequence(T)` whenever `S <= T`.
  // This definition is needed in the definition of the `Interference` and `Havoc` methods, and in the loop invariants of the `Run` methods.
  twostate predicate legalTransitionsSequence(running: set<Thread>) reads * {
    && baseLegalTransitionsSequence()
    // Version numbers only increase
    // Updated objects must obey their transitive 2-state invariants.
    && (forall o: Object | o in old(content) :: unchanged(o) || o.sequenceInv2())
    // Objects cannot change the nonvolatile fields if they are directly owned by threads that cannot run.
    // The 2-state invariant of OwnedObject extends this property to objects that are *transitively* owned by the threads.
    && (forall o: OwnedObject | o in old(content) && old(o.owner) is Thread ::
      // Threads created during a legalTransitionsSequence are allowed to run
      old(o.owner) as Thread !in running && old(allocated(o.owner)) ==> old(o.nonvolatileVersion) == o.nonvolatileVersion
    )
  }

  // A legal transition is one that starts from a good state, preserves the universe invariant, and meets the legality conditions.
  // This relation only needs to describe a *single* legal transition, not a sequence. So, it doesn't need to be
  // transitive and it can be more precise than `legalTransitionsSequence`.
  twostate predicate legalTransition(running: Thread) reads * {
    && legalTransitionsSequence({running})
    && old(globalInv())
    // The first condition for legality: old objects that change a field must obey their 1- and 2-state invariants.
    && (forall o: Object | o in old(content) :: unchanged(o) || (o.inv() && o.inv2()))
    // The second condition for legality: new objects must satisfy their invariants.
    && (forall o: Object | o in content && o !in old(content) :: o.inv())
  }

  // Transitive LCI soundness: legal transitions are good. This makes use of the admissibility obligations build into Object's.
  twostate lemma sequenceLci(running: set<Thread>)
    requires legalTransitionsSequence(running)
    ensures globalSequenceInv2()
  {
    forall o: Object | o in old(content) && o.goodPreAndLegalChangesSequence(running) ensures o.sequenceInv2() { o.sequenceAdmissibility(running); }
  }

  // LCI soundness: legal transitions are good. This makes use of the admissibility obligations build into Object's.
  twostate lemma lci(running: Thread)
    requires legalTransition(running)
    ensures globalInv() && globalInv2()
  {
    forall o: Object | o in old(content) && o.goodPreAndLegalChanges(running) ensures o.inv2() && o.inv() { o.admissibility(running); }
  }

  method Havoc()
    requires globalBaseInv()
    modifies this, this.content
    ensures globalBaseInv() && baseLegalTransitionsSequence()
  {
    // Do nothing. Just havoc stuff on the caller side.
  }

  // Model the preemption of a given thread. Any other thread will have a chance to execute any number of legal transitions,
  // modifying (1) volatile fiels of any object and (2) nonvolatile fields of objects that are not transitively owned by
  // the preempting thread.
  method Interference(preempting: Thread)
    requires globalInv() && preempting in content
    modifies this, this.content
    ensures globalInv()
    // Ensure that other threads executed any number of legal transitions.
    // Ensuring `globalInv2` would be wrong, because it's not guaranteed to be transitive.
    ensures legalTransitionsSequence(set t: Thread | t in old(content) && t != preempting) && globalSequenceInv2()
  {
    // This method could be bodyless. Checking the following implementation is just a consistency check.
    // The verifier will report errors in case `legalTransitionsSequence` is not transitive.
    var steps: int :| 0 <= steps;
    sequenceLci({});
    while (steps > 0)
      invariant globalInv() && legalTransitionsSequence(set t: Thread | t in old(content) && t != preempting) && globalSequenceInv2()
    {
      // A thread of the environment (if there is any) executes a single legal transition.
      var envThreads: set<Thread> := set t: Thread | t in content && t != preempting;
      if (|envThreads| > 0) {
        ghost var running: Thread :| running in envThreads;
        label preTransition:
        assert globalSequenceInv2(); // (1)
        Havoc();
        assume legalTransition@preTransition(running);
        lci@preTransition(running);
        assert globalSequenceInv2@preTransition(); // (2)
        // We cannot call a 3-state lemma to apply the transitivity of `forall o: Object ... o.sequenceInv2`, so we have to assume this, checking (1) and (2).
        assume baseLegalTransitionsSequence() ==> globalSequenceInv2();
      }
      steps := steps - 1;
    }
  }

  // Consistency check: baseLegalTransitionsSequence should be transitive.
  method CheckTransitiveBaseLegalTransitionsSequence()
    requires globalBaseInv()
    modifies this, content
    ensures baseLegalTransitionsSequence()
  {
    Havoc();
    Havoc();
  }

  // Consistency check: legalTransitionsSequence should be transitive.
  method CheckTransitiveLegalTransitionsSequence(running: set<Thread>)
    requires globalInv()
    modifies this, content
    ensures legalTransitionsSequence(running)
  {
    Havoc();
    assume legalTransitionsSequence(running);
    sequenceLci(running);
    assert globalSequenceInv2(); // (1)
    label mid:
    Havoc();
    assume legalTransitionsSequence@mid(running);
    sequenceLci@mid(running);
    assert globalSequenceInv2@mid(); // (2)
    // We cannot call a 3-state lemma to apply the transitivity of `sequenceInv2`, so we have to assume it, checking (1) and (2).
    assume baseLegalTransitionsSequence() ==> globalSequenceInv2();
  }

  // Consistency check: legalTransitionsSequence should be monotonic w.r.t. adding elements to `running`.
  twostate lemma CheckMonotonicLegalTransitionsSequence(running: set<Thread>, moreRunning: set<Thread>)
    requires running <= moreRunning
    requires legalTransitionsSequence(running)
    ensures legalTransitionsSequence(moreRunning)
  { }

  // method SmokeTestHavoc()
  //   requires globalInv()
  //   modifies this, content
  //   ensures false
  // {
  //   Havoc();
  // }

  // method SmokeTestInterference(running: Thread)
  //   requires globalInv() && running in content
  //   modifies this, content
  //   ensures false
  // {
  //   Interference(running);
  // }
}

// A generic object trait
trait Object {
  // Universe of which the Object is a member.
  // This should really be a constant, but I don't know how to do that while factoring out join below,
  // because traits can't have constructors.
  const universe: Universe

  // Global base invariant (from o's perspective)
  predicate objectGlobalBaseInv() reads * { this in universe.content && baseFieldsInv() && universe.globalBaseInv() }

  // Global invariant (from o's perspective) - I am in the universe and the universe is good. (This implies I am good also.)
  predicate objectGlobalInv() reads * { this in universe.content && universe.globalInv() }

  // Global 2-state invariant (from o's perspective).
  twostate predicate objectGlobalInv2() requires old(objectGlobalInv()) reads * { objectGlobalBaseInv() && universe.globalInv2() }

  predicate triggerAxioms() reads this ensures triggerAxioms() {
    assume (this is OwnedObject || this is Thread) && !(this is OwnedObject && this is Thread);
    && (this is OwnedObject || this is Thread)
    && !(this is OwnedObject && this is Thread)
  }

  // Join the universe
  method join()
    requires universe.globalBaseInv() && baseFieldsInv() && this as object != universe
    modifies universe
    ensures objectGlobalBaseInv() && universe.content == old(universe.content) + { this }
  {
    universe.content := universe.content + { this };
    forall o: Object | o in universe.content ensures o.baseFieldsInv() {
      o.baseFieldsInvMonotonicity();
    }
  }

  // Precondition for the sequence admissibility check.
  twostate predicate goodPreAndLegalChangesSequence(running: set<Thread>) reads * {
    && old(this in universe.content)
    && unchanged(this)
    && universe.legalTransitionsSequence(running)
  }

  // Precondition for the admissibility check.
  // This is broken into a separate predicate because Dafny currently doesn't allow adm.requires() in a 1-state context
  twostate predicate goodPreAndLegalChanges(running: Thread) reads * {
    && old(this in universe.content)
    && unchanged(this)
    && universe.legalTransition(running)
  }

  // To be implemented: 1-state invariant, 2-state invariant, admissibility proof...
  predicate isOwnedObject() // To prevent a class from extending both OwnedObject and Thread
  predicate baseFieldsInv() reads this, universe // All fields of this object are in the universe
  twostate lemma baseFieldsInvMonotonicity() requires old(baseFieldsInv()) && old(universe.content) <= universe.content && unchanged(this) ensures baseFieldsInv()
  predicate localInv() reads * ensures localInv() ==> objectGlobalBaseInv()
  twostate predicate localInv2() reads *
  predicate inv() ensures inv() ==> localInv() reads *
  twostate predicate sequenceInv2() reads * // This should be transitive. See `CheckSequenceInv2` below.
  twostate predicate inv2() ensures inv2() ==> localInv2() && sequenceInv2() reads *
  twostate lemma sequenceAdmissibility(running: set<Thread>) requires goodPreAndLegalChangesSequence(running) ensures sequenceInv2()
  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv()
}

class Thread extends Object {
  // To prevent a class from extending both OwnedObject and Thread
  predicate isOwnedObject() { false }

  predicate baseFieldsInv() reads this, universe {
    true
  }
  twostate lemma baseFieldsInvMonotonicity() requires old(baseFieldsInv()) && old(universe.content) <= universe.content && unchanged(this) ensures baseFieldsInv() {}

  predicate localInv() reads * {
    && objectGlobalBaseInv()
  }
  predicate inv() reads * ensures inv() ==> localInv() {
    && localInv()
  }

  twostate predicate localInv2() reads * {
    true
  }
  twostate predicate sequenceInv2() reads * {
    true
  }
  twostate predicate inv2() reads * ensures inv2() ==> localInv2() && sequenceInv2() {
    localInv2() && sequenceInv2()
  }

  twostate lemma sequenceAdmissibility(running: set<Thread>) requires goodPreAndLegalChangesSequence(running) ensures sequenceInv2() {}
  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {}

  // Check (trivial) transitivity of sequenceInv2()
  method CheckSequenceInv2()
    requires objectGlobalInv()
    modifies universe, universe.content
    ensures sequenceInv2()
  {
    universe.Havoc();
    assume universe.baseLegalTransitionsSequence() && forall o: Object | o in old(universe.content) :: o.sequenceInv2();
    label mid:
    universe.Havoc();
    assume universe.baseLegalTransitionsSequence@mid() && forall o: Object | o in old@mid(universe.content) :: o.sequenceInv2@mid();
  }

  // Here we require a thread to create a thread. Programs shold assume that an initial thread exists in the universe.
  constructor(universe: Universe, ghost running: Thread)
    requires universe.globalInv() && running in universe.content
    modifies universe
    ensures objectGlobalInv() && universe.globalInv2()
  {
    this.universe := universe;
    new;
    join();
    universe.lci(running);
  }
}

trait OwnedObject extends Object {
  ghost var nonvolatileVersion: int
  ghost var owner: Object // nonvolatile

  // To prevent a class from extending both OwnedObject and Thread
  predicate isOwnedObject() { true }

  twostate predicate unchangedNonvolatileFields() reads this {
    old(owner) == owner && unchangedNonvolatileUserFields()
  }

  predicate baseFieldsInv() reads this, universe {
    && owner in universe.content
    && baseUserFieldsInv()
  }
  twostate lemma baseFieldsInvMonotonicity() requires old(baseFieldsInv()) && old(universe.content) <= universe.content && unchanged(this) ensures baseFieldsInv() {
    baseUserFieldsInvMonotonicity();
    assert owner in universe.content;
  }

  predicate localInv() reads * {
    && objectGlobalBaseInv()
    && localUserInv()
  }
  predicate inv() reads * ensures inv() ==> localInv() {
    && localInv()
    && userInv()
  }

  twostate predicate localInv2() reads * {
    && localUserInv2()
  }

  twostate predicate sequenceInv2() reads * {
    && old(nonvolatileVersion) <= nonvolatileVersion
    && (old(nonvolatileVersion) == nonvolatileVersion ==>
      // Nonvolatile fields are only allowed to change when the nonvolatileVersion changes.
      // TODO: This could be optimized by making the nonvolatile fields a version of the nonvolatile version number
      && unchangedNonvolatileFields()
      // Transitivity: if a nonvolatileVersion doesn't change, the same should apply to all owned objects
      //&& (forall o: OwnedObject | o in old(universe.content) && old(o.owner) == this :: old(o.nonvolatileVersion) == o.nonvolatileVersion && o.owner == this) // FIXME: This might be expensive
    )
    // The nonvolatileVersion cannot change if the version of the old owner doesn't change.
    && (old(owner) is OwnedObject ==>
      var oldOwner := old(owner) as OwnedObject;
      old(oldOwner.nonvolatileVersion) == oldOwner.nonvolatileVersion ==> old(nonvolatileVersion) == nonvolatileVersion
    )
    // The nonvolatileVersion cannot change if the version of the new owner doesn't change.
    // Note: this is inconvenient. Receiving ownership shouldn't require to change the nonvolatile version.
    // && (owner is OwnedObject ==>
    //   var newOwner := owner as OwnedObject;
    //   old(allocated(newOwner)) && old(newOwner.nonvolatileVersion) == newOwner.nonvolatileVersion ==> old(nonvolatileVersion) == nonvolatileVersion
    // )
  }

  twostate predicate inv2() reads * ensures inv2() ==> localInv2() && sequenceInv2() {
    && localInv2()
    && sequenceInv2()
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

  // Check transitivity of sequenceInv2()
  method CheckSequenceInv2()
    requires objectGlobalInv()
    modifies universe, universe.content
    ensures sequenceInv2()
  {
    universe.Havoc();
    assume universe.baseLegalTransitionsSequence() && forall o: Object | o in old(universe.content) :: o.sequenceInv2();
    var u1 := unchangedNonvolatileFields(); // (1)
    label mid:
    universe.Havoc();
    assume universe.baseLegalTransitionsSequence@mid() && forall o: Object | o in old@mid(universe.content) :: o.sequenceInv2@mid();
    var u2 := unchangedNonvolatileFields@mid(); // (2)
    // We cannot call a 3-state lemma to apply the transitivity of `unchangedNonvolatileFields`, so we have to assume it.
    assume u1 && u2 ==> unchangedNonvolatileFields();
  }

  // To be implemented in the class: 1-state invariant, 2-state invariant, admissibility proof...
  predicate baseUserFieldsInv() reads this, universe
  twostate lemma baseUserFieldsInvMonotonicity() requires old(baseUserFieldsInv()) && old(universe.content) <= universe.content && unchanged(this) ensures baseUserFieldsInv()
  twostate predicate unchangedNonvolatileUserFields() reads this // Checking transitivity is up to the classes that implement this trait.
  predicate localUserInv() reads *
  twostate predicate localUserInv2() reads *
  predicate userInv() reads * ensures userInv() ==> localUserInv()
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2()

  // Every class should check the transitivity of unchangedNonvolatileFields():
  // method CheckTransitiveUnchangedNonvolatileFields()
  //   modifies universe, universe.content
  //   ensures unchangedNonvolatileFields()
  // {
  //   universe.Havoc();
  //   assume unchangedNonvolatileFields();
  //   label mid:
  //   universe.Havoc();
  //   assume unchangedNonvolatileFields@mid();
  // }
}

method BumpVersion(ghost last: int) returns (res: int) ensures res > last

// A strictly increasing counter
class IncreasingCounter extends OwnedObject {
  var value: int // volatile

  predicate baseUserFieldsInv() reads this, universe { true }
  twostate lemma baseUserFieldsInvMonotonicity() requires old(baseUserFieldsInv()) && old(universe.content) <= universe.content && unchanged(this) ensures baseUserFieldsInv() {}

  twostate predicate unchangedNonvolatileUserFields() reads this { true }

  predicate localUserInv() reads * {
    && true
  }
  predicate userInv() reads * ensures userInv() ==> localUserInv() {
    && localUserInv()
  }

  twostate predicate localUserInv2() reads * {
    old(value) <= value
  }
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2() {
    && localUserInv2()
  }

  twostate lemma sequenceAdmissibility(running: set<Thread>) requires goodPreAndLegalChangesSequence(running) ensures sequenceInv2() {}
  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {}

  constructor(universe: Universe, ghost running: Thread, value: int)
    requires universe.globalInv() && running in universe.content
    modifies universe
    ensures objectGlobalInv() && universe.globalInv2()
    // The following might not always be needed
    ensures this.universe == universe && this.owner == running && this.value == value
    ensures universe.content == old(universe.content) + { this }
  {
    this.universe := universe;
    this.value := value;
    this.owner := running;
    new;
    join();
    universe.lci(running);
  }
}

class Integer extends OwnedObject {
  var value: int // nonvolatile

  predicate baseUserFieldsInv() reads this, universe { true }
  twostate lemma baseUserFieldsInvMonotonicity() requires old(baseUserFieldsInv()) && old(universe.content) <= universe.content && unchanged(this) ensures baseUserFieldsInv() {}

  twostate predicate unchangedNonvolatileUserFields() reads this {
    old(value) == value
  }

  predicate localUserInv() reads * {
    && true
  }
  predicate userInv() reads * ensures userInv() ==> localUserInv() {
    && localUserInv()
  }

  twostate predicate localUserInv2() reads * {
    && true
  }
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2() {
    && localUserInv2()
  }

  twostate lemma sequenceAdmissibility(running: set<Thread>) requires goodPreAndLegalChangesSequence(running) ensures sequenceInv2() {}
  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {}

  constructor(universe: Universe, ghost running: Thread, value: int)
    requires universe.globalInv() && running in universe.content
    modifies universe
    ensures objectGlobalInv() && universe.globalInv2()
    // The following might not always be needed
    ensures this.universe == universe && this.owner == running && this.value == value
    ensures universe.content == old(universe.content) + { this }
  {
    this.universe := universe;
    this.value := value;
    this.owner := running;
    new;
    join();
    universe.lci(running);
  }
}

class ConstantInteger extends OwnedObject {
  var value: int // nonvolatile

  predicate baseUserFieldsInv() reads this, universe { true }
  twostate lemma baseUserFieldsInvMonotonicity() requires old(baseUserFieldsInv()) && old(universe.content) <= universe.content && unchanged(this) ensures baseUserFieldsInv() {}

  twostate predicate unchangedNonvolatileUserFields() reads this {
    old(value) == value
  }

  predicate localUserInv() reads * {
    && true
  }
  predicate userInv() reads * ensures userInv() ==> localUserInv() {
    && localUserInv()
  }

  twostate predicate localUserInv2() reads * {
    && old(value) == value
  }
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2() {
    && localUserInv2()
  }

  twostate lemma sequenceAdmissibility(running: set<Thread>) requires goodPreAndLegalChangesSequence(running) ensures sequenceInv2() {}
  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {}

  constructor(universe: Universe, ghost running: Thread, value: int)
    requires universe.globalInv() && running in universe.content
    modifies universe
    ensures objectGlobalInv() && universe.globalInv2()
    // The following might not always be needed
    ensures this.universe == universe && this.owner == running && this.value == value
    ensures universe.content == old(universe.content) + { this }
  {
    this.universe := universe;
    this.value := value;
    this.owner := running;
    new;
    join();
    universe.lci(running);
  }
}

class ClaimIncreasingCounterGreaterThanConstant extends OwnedObject {
  var counter: IncreasingCounter // nonvolatile
  var constant: ConstantInteger // nonvolatile

  predicate baseUserFieldsInv() reads this, universe {
    && counter in universe.content
    && constant in universe.content
  }
  twostate lemma baseUserFieldsInvMonotonicity() requires old(baseUserFieldsInv()) && old(universe.content) <= universe.content && unchanged(this) ensures baseUserFieldsInv() {}

  twostate predicate unchangedNonvolatileUserFields() reads this {
    old(counter) == counter && old(constant) == constant
  }

  predicate localUserInv() reads * {
    && counter.value >= constant.value
  }
  predicate userInv() reads * ensures userInv() ==> localUserInv() {
    && localUserInv()
  }

  twostate predicate localUserInv2() reads * {
    && old(counter) == counter
    && old(constant) == constant
  }
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2() {
    && localUserInv2()
  }

  twostate lemma sequenceAdmissibility(running: set<Thread>) requires goodPreAndLegalChangesSequence(running) ensures sequenceInv2() {}
  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {}

  constructor(universe: Universe, ghost running: Thread, counter: IncreasingCounter, constant: ConstantInteger)
    requires universe.globalInv() && running in universe.content && counter in universe.content && constant in universe.content
    requires counter.value >= constant.value
    modifies universe
    ensures objectGlobalInv() && universe.globalInv2()
    // The following might not always be needed
    ensures this.universe == universe && this.owner == running && this.counter == counter && this.constant == constant
    ensures universe.content == old(universe.content) + { this }
  {
    this.universe := universe;
    this.owner := running;
    this.counter := counter;
    this.constant := constant;
    new;
    join();
    universe.lci(running);
  }
}

// Note: the translation from Rust types to Dafny is done manually, in this file. For example, all Rust primitive types
// should have been translated to a Dafny class in order to allow specifying an owner.
//
// fn incrementer(counter: Arc<AtomicIsize>, remaining: &mut isize)
//   requires *remaining == 10
//   ensures *remaining == 0
// {
//   let mut i = 0;
//   while i < 10 {
//     label l2:
//     let initial_value = counter.load(SeqCst);
//     counter.fetch_add(1, SeqCst);
//     let final_value = counter.load(SeqCst);
//     assert!(final_value >= initial_value + 1);
//     i += 1;
//     *remaining -= 1;
//   }
//   assert!(i == 10);
// }

method Incrementer(universe: Universe, running: Thread, counter: IncreasingCounter, remaining: Integer)
   requires universe.globalInv() && running in universe.content && counter in universe.content && remaining in universe.content
   requires remaining.owner == running && remaining.value == 10 // USER precondition
   modifies universe, universe.content
   ensures universe.globalInv() && universe.baseLegalTransitionsSequence()
   ensures remaining.value == 0 // USER postcondition
{
  universe.Interference(running);

  label l0:
  var i := 0;
  universe.lci@l0(running);

  universe.Interference(running);

  label l1:
  while i < 10
    modifies universe, universe.content
    invariant universe.globalInv();
    invariant universe.baseLegalTransitionsSequence@l1();
    //invariant universe.baseLegalTransitionsSequence();
    invariant remaining.owner == running && 0 <= i && i + remaining.value == 10; // USER invariant
  {
    label l2:
    var initial_value := new ConstantInteger(universe, running, counter.value);
    var claim1 := new ClaimIncreasingCounterGreaterThanConstant(universe, running, counter, initial_value);
    universe.lci@l2(running);

    universe.Interference(running);

    label l3:
    counter.value := counter.value + 1;
    universe.lci@l3(running);
    
    // No interference!

    label l3p1:
    var initial_value_plus_one := new ConstantInteger(universe, running, initial_value.value + 1);
    universe.lci@l3p1(running);
    
    // No interference!

    label l3p2:
    // assert claim1.inv(); // Help Dafny (1)
    // assert {:split_here} claim1.counter == counter && claim1.constant == initial_value; // Help Dafny (1)
    var claim2 := new ClaimIncreasingCounterGreaterThanConstant(universe, running, counter, initial_value_plus_one);
    universe.lci@l3p2(running);

    universe.Interference(running);

    label l4:
    // assert claim2.inv(); // Help Dafny (1)
    // assert {:split_here} claim2.counter == counter && claim2.constant == initial_value_plus_one; // Help Dafny (1)
    var final_value := new ConstantInteger(universe, running, counter.value);
    universe.lci@l4(running);

    universe.Interference(running);

    label l5:
    // assert claim1.inv(); // Help Dafny (1)
    // assert claim2.inv(); // Help Dafny (1)
    // assert claim1.counter == counter && claim1.constant == initial_value; // Help Dafny (1)
    // assert claim2.counter == counter && claim2.constant == initial_value_plus_one; // Help Dafny (1)
    // assert initial_value_plus_one.value == initial_value.value + 1; // Help Dafny (1)
    // assert final_value.value >= initial_value.value + 1; // Help Dafny (1)
    assert {:split_here} true;
    universe.lci@l5(running);

    universe.Interference(running);

    label l6:
    i := i + 1;
    universe.lci@l6(running);

    universe.Interference(running);

    assume false; // FIXME the following code takes too long to verify; something has to be fixed.

    label l7:
    assert {:split_here} remaining.owner == running; // Help Dafny?
    assert {:split_here} running.triggerAxioms(); // Help Dafny?
    remaining.value := remaining.value - 1;
    remaining.nonvolatileVersion := BumpVersion(remaining.nonvolatileVersion);
    assert {:split_here} remaining.inv2@l7(); // Help Dafny?
    assert {:split_here} universe.baseLegalTransitionsSequence@l7(); // Help Dafny?
    assert {:split_here} universe.legalTransitionsSequence@l7({running}); // Help Dafny?
    assert {:split_here} universe.legalTransition@l7(running); // Help Dafny?
    universe.lci@l7(running);

    universe.Interference(running);
  }

  universe.Interference(running);

  label l8:
  assert i == 10;
  universe.lci@l8(running);

  universe.Interference(running);
}
