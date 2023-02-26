// RUN: %dafny /compile:0 /proverOpt:O:smt.qi.eager_threshold=30 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This program models the ownership of a Rust-like MutexGuard.
// To speed up the verification: /vcsLoad:0.5 /proverOpt:O:smt.qi.eager_threshold=30

// A universe of objects playing under LCI rules
trait Universe {
  // The set of objects in the universe
  var content: set<Object>

  // Universe invariant: the universe doesn't contain itself,
  // and its objects in this universe agree that they are in this universe.
  // We define this to allow a generic object operation (Object.join below) to add the object to the universe,
  // without having to check the object invariants.
  ghost predicate globalBaseInv() reads this, content {
    && (forall o: Object | o in content :: o.universe == this && o as object != this && o.baseFieldsInv() && o.triggerAxioms())
  }

  // Global 1-state invariant: all objects satisfy their individual invariants.
  ghost predicate globalInv() reads * {
    globalBaseInv() && (forall o: Object | o in content :: o.inv())
  }

  // Global transitive 2-state invariant: all old objects satisfy their transitive 2-state invariants.
  twostate predicate globalSequenceInv2() reads * {
    forall o: Object | o in old(content) :: o in content && o.sequenceInv2()
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
    // fresh(content - old(content)) // This is slow. Dafny is 20x faster using the following quantifier!
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
    && (forall o: Object | o in old(content) && o in content :: unchanged(o) || o.sequenceInv2()) // `o in content` adds a useful trigger
    // Objects cannot change the nonvolatile fields if they are directly owned by threads that cannot run.
    // The 2-state invariant of OwnedObject extends this property to objects that are *transitively* owned by the threads.
    && (forall o: OwnedObject | o in old(content) && old(o.owner) is Thread ::
      // Threads created during a legalTransitionsSequence are allowed to run
      old(o.owner) as Thread !in running && old(allocated(o.owner)) ==> old(o.nonvolatileVersion) == o.nonvolatileVersion
    )
  }

  twostate predicate legalTransitionsSequenceAnyThread() reads * {
    legalTransitionsSequence(set t: Thread | t in old(content))
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

  // Transitive LCI soundness
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
  //   ensures false // Should fail
  // {
  //   Havoc();
  // }

  // method SmokeTestInterference(running: Thread)
  //   requires globalInv() && running in content
  //   modifies this, content
  //   ensures false // Should fail
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
  ghost predicate objectGlobalBaseInv() reads * { this in universe.content && baseFieldsInv() && universe.globalBaseInv() }

  // Global invariant (from o's perspective) - I am in the universe and the universe is good. (This implies I am good also.)
  ghost predicate objectGlobalInv() reads * { this in universe.content && universe.globalInv() }

  // Global 2-state invariant (from o's perspective).
  twostate predicate objectGlobalInv2() requires old(objectGlobalInv()) reads * { objectGlobalBaseInv() && universe.globalInv2() }

  ghost predicate triggerAxioms() reads this ensures triggerAxioms() {
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
  ghost predicate isOwnedObject() // To prevent a class from extending both OwnedObject and Thread
  ghost predicate baseFieldsInv() reads this, universe // All fields of this object are in the universe
  twostate lemma baseFieldsInvMonotonicity() requires old(baseFieldsInv()) && old(universe.content) <= universe.content && unchanged(this) ensures baseFieldsInv()
  ghost predicate localInv() reads * ensures localInv() ==> objectGlobalBaseInv()
  twostate predicate localInv2() reads *
  ghost predicate inv() ensures inv() ==> localInv() reads *
  twostate predicate sequenceInv2() reads * // This should be transitive. See `CheckSequenceInv2` below.
  twostate predicate inv2() ensures inv2() ==> localInv2() && sequenceInv2() reads *
  twostate lemma sequenceAdmissibility(running: set<Thread>) requires goodPreAndLegalChangesSequence(running) ensures sequenceInv2()
  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv()
}

class Thread extends Object {
  // To prevent a class from extending both OwnedObject and Thread
  ghost predicate isOwnedObject() { false }

  ghost predicate baseFieldsInv() reads this, universe {
    true
  }
  twostate lemma baseFieldsInvMonotonicity() requires old(baseFieldsInv()) && old(universe.content) <= universe.content && unchanged(this) ensures baseFieldsInv() {}

  ghost predicate localInv() reads * ensures localInv() ==> objectGlobalBaseInv() {
    && objectGlobalBaseInv()
  }
  ghost predicate inv() reads * ensures inv() ==> localInv() {
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
    ensures objectGlobalInv() && universe.legalTransition(running)
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

  // If true, any thread can take ownership of the object and change its nonvolatile fields.
  // If false, only the owner can modify the nonvolatile fields.
  // Intended usage: This should be set to true when a thread wants to let any thread to take ownership of the object.
  //ghost var stealable: bool // nonvolatile

  // To prevent a class from extending both OwnedObject and Thread
  ghost predicate isOwnedObject() { true }

  ghost predicate baseFieldsInv() reads this, universe {
    && owner in universe.content
    && baseUserFieldsInv()
  }
  twostate lemma baseFieldsInvMonotonicity() requires old(baseFieldsInv()) && old(universe.content) <= universe.content && unchanged(this) ensures baseFieldsInv() {
    baseUserFieldsInvMonotonicity();
  }

  twostate predicate unchangedNonvolatileFields() reads this {
    && old(owner) == owner
    && unchangedNonvolatileUserFields()
  }

  ghost predicate localInv() reads * ensures localInv() ==> objectGlobalBaseInv() {
    && objectGlobalBaseInv()
    && localUserInv()
  }
  ghost predicate inv() reads * ensures inv() ==> localInv() {
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
      //&& (forall o: OwnedObject | o in old(universe.content) && old(o.owner) == this :: old(o.nonvolatileVersion) == o.nonvolatileVersion)
    )
    // The nonvolatileVersion cannot change if the version of the old owner doesn't change.
    && (old(owner) is OwnedObject ==>
      var oldOwner := old(owner) as OwnedObject;
      !oldOwner.volatileOwns() && old(oldOwner.nonvolatileVersion) == oldOwner.nonvolatileVersion ==> old(nonvolatileVersion) == nonvolatileVersion
    )
    // The nonvolatileVersion cannot change if the version of the new owner doesn't change.
    // Note: this seems fine, but unnecessary.
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
  ghost predicate volatileOwns() // If true, the set of owned objects can change without changing the nonvolatileVersion
  ghost predicate baseUserFieldsInv() reads this, universe
  twostate lemma baseUserFieldsInvMonotonicity() requires old(baseUserFieldsInv()) && old(universe.content) <= universe.content && unchanged(this) ensures baseUserFieldsInv()
  twostate predicate unchangedNonvolatileUserFields() reads this // Checking transitivity is up to the classes that implement this trait.
  ghost predicate localUserInv() reads *
  twostate predicate localUserInv2() reads *
  ghost predicate userInv() reads * ensures userInv() ==> localUserInv()
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

// fn test(m: Arc<Mutex<u32>>) {
//   let l: MutexGuard<T> = m.lock().unwrap(); // create a guard == acquire mutex
//   let a: u32 = *l;
//   let b: u32 = *l;
//   assert!(a == b); // Ensured
//   drop(l); // deallocate a guard == release mutex
// }

// An owned integer type
class OwnedU32 extends OwnedObject {
  var value: int // nonvolatile

  ghost predicate volatileOwns() { false }
  ghost predicate baseUserFieldsInv() reads this, universe { true }
  twostate lemma baseUserFieldsInvMonotonicity() requires old(baseUserFieldsInv()) && old(universe.content) <= universe.content && unchanged(this) ensures baseUserFieldsInv() {}

  twostate predicate unchangedNonvolatileUserFields() reads this {
    && old(value) == value
  }

  ghost predicate localUserInv() reads * { true }
  ghost predicate userInv() reads * ensures userInv() ==> localUserInv() { localUserInv() }
  twostate predicate localUserInv2() reads * { true }
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2() { localUserInv2() }

  twostate lemma sequenceAdmissibility(running: set<Thread>) requires goodPreAndLegalChangesSequence(running) ensures sequenceInv2() {}
  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {}

  constructor(universe: Universe, ghost running: Thread, value: int)
    requires universe.globalInv() && running in universe.content
    modifies universe
    ensures objectGlobalInv() && universe.legalTransition(running)
    ensures this.universe == universe && this.owner == running && this.value == value
    ensures universe.content == old(universe.content) + { this }
  {
    this.universe := universe;
    this.owner := running;
    this.value := value;
    new;
    join();
    universe.lci(running);
  }
}

class Mutex extends OwnedObject {
  var data: OwnedU32 // volatile (it was UnsafeCell<u32>)
  var locked: bool // volatile (it was UnsafeCell<bool>)
  ghost var guards: set<MutexGuardU32> // volatile

  ghost predicate volatileOwns() { true }
  ghost predicate baseUserFieldsInv() reads this, universe {
    && data in universe.content
    && guards <= universe.content
  }
  twostate lemma baseUserFieldsInvMonotonicity() requires old(baseUserFieldsInv()) && old(universe.content) <= universe.content && unchanged(this) ensures baseUserFieldsInv() {}

  twostate predicate unchangedNonvolatileUserFields() reads this { true }

  ghost predicate localUserInv() reads * {
    && (locked ==>
      && data.owner is MutexGuardU32
      && (data.owner as MutexGuardU32).mutex == this
      && guards == { data.owner as MutexGuardU32 }
    )
    && (!locked ==>
      && data.owner == this
      && guards == {}
    )
  }
  ghost predicate userInv() reads * ensures userInv() ==> localUserInv() {
    && localUserInv()
    && (forall g: MutexGuardU32 | g in guards :: g.localInv())
  }
  twostate predicate localUserInv2() reads * { 
    && old(data) == data
  }
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2() {
    && localUserInv2()
    //&& (forall g: MutexGuardU32 | g in old(guards) :: g.localInv2())
  }

  twostate lemma sequenceAdmissibility(running: set<Thread>) requires goodPreAndLegalChangesSequence(running) ensures sequenceInv2() {}
  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {
    assert userInv();
  }

  constructor(universe: Universe, ghost running: Thread, data: OwnedU32)
    requires universe.globalInv() && running in universe.content && data in universe.content && data.owner == running
    modifies universe, data
    ensures objectGlobalInv() && universe.legalTransition(running)
    ensures this.universe == universe && this.owner == running && this.data == data && !this.locked
    ensures universe.content == old(universe.content) + { this }
  {
    this.universe := universe;
    this.owner := running;
    this.data := data;
    this.locked := false;
    this.guards := {};
    new;
    join();
    // Transfer ownership of `this.data` from `running` to `this`.
    this.data.owner := this;
    this.data.nonvolatileVersion := BumpVersion(this.data.nonvolatileVersion);
    universe.lci(running);
  }
}

class MutexGuardU32 extends OwnedObject {
  var mutex: Mutex // nonvolatile
  ghost var data: OwnedU32 // nonvolatile

  ghost predicate volatileOwns() { false }
  ghost predicate baseUserFieldsInv() reads this, universe {
    && mutex in universe.content
    && data in universe.content
  }
  twostate lemma baseUserFieldsInvMonotonicity() requires old(baseUserFieldsInv()) && old(universe.content) <= universe.content && unchanged(this) ensures baseUserFieldsInv() {}

  twostate predicate unchangedNonvolatileUserFields() reads this {
    && old(mutex) == mutex
    && old(data) == data
  }

  ghost predicate localUserInv() reads * {
    && mutex.locked
    && mutex.guards == { this }
    && mutex.data.owner == this
    && mutex.data == data
  }
  ghost predicate userInv() reads * ensures userInv() ==> localUserInv() {
    && localUserInv()
    && mutex.localInv()
  }
  twostate predicate localUserInv2() reads * {
    && old(mutex) == mutex
  }
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2() {
    && localUserInv2()
    && mutex.localInv2()
  }

  twostate lemma sequenceAdmissibility(running: set<Thread>) requires goodPreAndLegalChangesSequence(running) ensures sequenceInv2() {}
  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {}

  constructor(universe: Universe, ghost running: Thread, mutex: Mutex)
    requires universe.globalInv() && running in universe.content && mutex in universe.content
    requires !mutex.locked
    modifies universe, mutex`locked, mutex`guards, mutex.data`owner, mutex.data`nonvolatileVersion
    ensures objectGlobalInv() && universe.legalTransition(running)
    ensures this.universe == universe && this.owner == running && this.mutex == mutex && this.data == mutex.data && this.mutex.locked && this.mutex.data.owner == this
    ensures universe.content == old(universe.content) + { this }
  {
    this.universe := universe;
    this.owner := running;
    this.mutex := mutex;
    this.data := mutex.data;
    new;
    join();
    // Acquire the lock
    this.mutex.locked := true;
    this.mutex.guards := { this };
    // Transfer ownership of `this.mutex.data` from `this.mutex` to `this`.
    this.mutex.data.owner := this;
    this.mutex.data.nonvolatileVersion := BumpVersion(this.mutex.data.nonvolatileVersion);
    // We don't need to bump this.mutex.nonvolatileVersion, because it uses volatileOwns.
    universe.lci(running);
  }
}

method Acquire(universe: Universe, running: Thread, mutex: Mutex)
  returns (guard: MutexGuardU32)
  requires universe.globalInv() && running in universe.content && mutex in universe.content
  modifies universe, universe.content
  decreases *
  // Instead of `baseLegalTransitionsSequence`, `legalTransitionsSequenceAnyThread` would be more precise and complete.
  ensures universe.globalInv() && universe.baseLegalTransitionsSequence()
  ensures guard in universe.content
  ensures guard.owner == running && guard.mutex == mutex
{
  universe.Interference(running);
  assert {:split_here} true;

  label lci_l11:
  var wasLocked := mutex.locked;
  universe.lci@lci_l11(running);
  assert {:split_here} true;

  // No interference

  label beforeLoop:
  while (wasLocked)
    modifies universe, universe.content
    invariant universe.globalInv() && universe.baseLegalTransitionsSequence@beforeLoop();
    invariant !wasLocked ==> !mutex.locked
    decreases * // Nothing guarantees that we'll obtain the lock
  {
    universe.Interference(running);
    assert {:split_here} true;

    label lci_l12:
    wasLocked := mutex.locked;
    universe.lci@lci_l12(running);
    assert {:split_here} true;
  }
  assert {:split_here} true;

  // No interference

  label lci_l13:
  guard := new MutexGuardU32(universe, running, mutex);
  universe.lci@lci_l13(running);
  assert {:split_here} true;

  universe.Interference(running);
  assert {:split_here} true;
}

// fn set_data(m: Arc<Mutex<u32>>) {
//   let l: MutexGuard<T> = m.lock().unwrap(); // create a guard == acquire mutex
//   let a: u32 = *l;
//   let b: u32 = *l;
//   assert!(a == b); // Ensured
//   *l = 42;
//   drop(l); // deallocate a guard == release mutex
// }

method {:vcs_split_on_every_assert} SetData(universe: Universe, running: Thread, mutex: Mutex)
  requires universe.globalInv() && running in universe.content && mutex in universe.content
  modifies universe, universe.content
  decreases *
  ensures universe.globalInv() && universe.baseLegalTransitionsSequence()
{
  universe.Interference(running);
  assert {:split_here} true;

  // A method call is not a single atomic step.
  var guard := Acquire(universe, running, mutex);
  assert {:split_here} true;

  universe.Interference(running);
  assert {:split_here} true;

  label lci_l14:
  var a := guard.mutex.data.value;
  universe.lci@lci_l14(running);
  assert {:split_here} true;

  universe.Interference(running);
  assert {:split_here} true;

  label lci_l15:
  var b := guard.mutex.data.value;
  universe.lci@lci_l15(running);
  assert {:split_here} true;

  universe.Interference(running);
  assert {:split_here} true;

  label lci_l16:
  assert a == b;
  universe.lci@lci_l16(running);
  assert {:split_here} true;

  universe.Interference(running);
  assert {:split_here} true;

  label lci_l17:
  guard.mutex.data.value := 42;
  guard.mutex.data.nonvolatileVersion := BumpVersion(guard.mutex.data.nonvolatileVersion);
  guard.nonvolatileVersion := BumpVersion(guard.nonvolatileVersion);
  universe.lci@lci_l17(running);
  assert {:split_here} true;

  universe.Interference(running);
  assert {:split_here} true;

  // TODO: deallocate guard
}

// fn main() {
//   let data = 0;
//   let mutex = MutexGuard::new(data)
//   client(mutex)
// }

method Main(universe: Universe, running: Thread)
  requires universe.globalInv() && running in universe.content // or, universe.content == { running }
  modifies universe, universe.content
  decreases *
  ensures universe.globalInv() && universe.baseLegalTransitionsSequence()
{
  universe.Interference(running);
  assert {:split_here} true;

  label lci_l1:
  var data := new OwnedU32(universe, running, 0);
  universe.lci@lci_l1(running);
  assert {:split_here} true;

  label lci_l2:
  var mutex := new Mutex(universe, running, data);
  universe.lci@lci_l2(running);
  assert {:split_here} true;

  // A method call is not a single atomic step.
  SetData(universe, running, mutex);

  universe.Interference(running);
  assert {:split_here} true;
}
