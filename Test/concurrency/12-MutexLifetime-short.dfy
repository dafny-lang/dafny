// RUN: %dafny /compile:0 /proverOpt:O:smt.qi.eager_threshold=30 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This program models the ownership of a Rust-like MutexGuard using lifetimes to reason about allocation.
// To speed up the verification: /vcsLoad:0.5 /proverOpt:O:smt.qi.eager_threshold=30

// A universe of objects playing under LCI rules
trait Universe {
  // The set of objects in the universe
  ghost var content: set<Object>

  // Universe invariant: the universe doesn't contain itself,
  // and its objects in this universe agree that they are in this universe.
  // We define this to allow a generic object operation (O.join below) to add the object to the universe,
  // without having to check the object invariants.
  predicate globalBaseInv() reads this, content {
    && (forall o: Object | o in content ::
      o.universe == this && o as object != this && o.baseFieldsInv() && o.triggerAxioms())
  }

  // Global 1-state invariant: all objects satisfy their individual invariants.
  predicate globalInv() reads * {
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
    && (forall o: Object | o !in old(content) && o in content :: !old(allocated(o)))
  }

  // This relation describes a sequence of legal transitions, each of which can be performed by a newly created thread
  // or by one of the threads in the `running` parameter.
  // This definition is weaker than `legalTransition`, but it's transitive (if it holds for A->B and B->C then it holds also for A->C).
  // This definition is also monotonic w.r.t. `running`: `legalTransitionsSequence(S)` should imply `legalTransitionsSequence(T)` whenever `S <= T`.
  // This definition is needed in the definition of the `Interference` and `Havoc` methods, and in the loop invariants of the `Run` methods.
  twostate predicate legalTransitionsSequence(running: set<Thread>) reads * {
    && baseLegalTransitionsSequence()
    && running <= old(content)
    // Optional feature: the universe can only change if there are threads that can run
    // && (running == {} ==> unchanged(this`content) && unchanged(content))
    // Version numbers only increase
    // Updated objects must obey their transitive 2-state invariants.
    && (forall o: Object | o in old(content) && o in content :: unchanged(o) || o.sequenceInv2())
    // Objects cannot change the nonvolatile fields if they are directly owned by threads that cannot run.
    // The 2-state invariant of OwnedObject extends this property to objects that are *transitively* owned by the threads.
    && (forall o: OwnedObject | o in old(content) && old(o.owner) is Thread ::
      // Threads created during a legalTransitionsSequence are allowed to run
      old(o.owner) as Thread !in running && old(allocated(o.owner)) ==> old(o.nonvolatileVersion) == o.nonvolatileVersion
    )
    // Nonvolatile fields of lifetimes cannot be changed by non-running threads.
    // TODO: This could be unified with the `nonvolatileVersion` mechanism.
    && (forall l: Lifetime | l in old(content) :: old(l.owner) !in running && old(allocated(l.owner)) ==> l.unchangedNonvolatileFields())
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

  // Consistency check: baseLegalTransitionsSequence should be transitive.
  method CheckTransitiveBaseLegalTransitionsSequence()
    requires globalBaseInv()
    modifies this, content
    ensures baseLegalTransitionsSequence()
  {
    Havoc(this);
    Havoc(this);
  }

  // Consistency check: legalTransitionsSequence should be transitive.
  method CheckTransitiveLegalTransitionsSequence(running: set<Thread>)
    requires globalInv()
    modifies this, content
    ensures legalTransitionsSequence(running)
  {
    Havoc(this);
    assume legalTransitionsSequence(running);
    sequenceLci(running);
    assert globalSequenceInv2(); // (1)
    label mid:
    Havoc(this);
    assume legalTransitionsSequence@mid(running);
    sequenceLci@mid(running);
    assert globalSequenceInv2@mid(); // (2)
    // We cannot call a 3-state lemma to apply the transitivity of `sequenceInv2`, so we have to assume it, checking (1) and (2).
    assume baseLegalTransitionsSequence() ==> globalSequenceInv2();
  }

  // Consistency check: legalTransitionsSequence should be monotonic w.r.t. adding elements to `running`.
  twostate lemma CheckMonotonicLegalTransitionsSequence(running: set<Thread>, moreRunning: set<Thread>)
    requires running <= moreRunning <= old(content)
    requires legalTransitionsSequence(running)
    ensures legalTransitionsSequence(moreRunning)
    ensures legalTransitionsSequenceAnyThread()
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

  // The constructor should magically ensure that the universe contains the thread running the main function.

  least predicate outlives[nat](a: Lifetime, b: Lifetime)
    reads this, (set l: Lifetime | l in content)`mightPointTo, (set l: Lifetime | l in content)`mightPointFrom
    requires a in content && b in content
  {
    a in b.mightPointTo || (exists x: Lifetime | x in content :: outlivesThrough(a, x, b))
  }

  least predicate outlivesThrough[nat](a: Lifetime, x: Lifetime, b: Lifetime)
    reads this, (set l: Lifetime | l in content)`mightPointTo, (set l: Lifetime | l in content)`mightPointFrom
    requires a in content && x in content && b in content
  {
    (x in a.mightPointFrom || x in b.mightPointTo) && outlives(a, x) && outlives(x, b)
  }

  lemma OutlivesImpliesAlive()
    requires globalInv()
    ensures forall a, b: Lifetime {:trigger outlives(a, b)} | a in content && b in content ::
      outlives(a, b) && b.alive() ==> a.alive()
  {
    forall a, b: Lifetime | a in content && b in content && outlives(a, b) && b.alive()
      ensures a.alive()
    {
      var k: nat :| old(outlives#[k](a, b));
      OutlivesImpliesAliveHelper(a, b, k);
    }
  }

  lemma OutlivesImpliesAliveHelper(a: Lifetime, b: Lifetime, k: nat)
    requires globalInv() && a in content && b in content && outlives#[k](a, b)
    ensures b.alive() ==> a.alive()
  {
    if (k > 0) {
      if (a !in b.mightPointTo) {
        var x: Lifetime :| x in content && outlivesThrough#[k-1](a, x, b);
        OutlivesImpliesAliveHelper(a, x, k-2);
        OutlivesImpliesAliveHelper(x, b, k-2);
      }
    }
  }

  twostate lemma FrameOutlives()
    requires old(content) <= content
    requires forall l: Lifetime | l in old(content) :: old(l.mightPointFrom) <= l.mightPointFrom && old(l.mightPointTo) <= l.mightPointTo
    ensures forall a, b: Lifetime | a in old(content) && b in old(content) :: old(outlives(a, b)) ==> outlives(a, b)
  {
    var running := set t: Thread | t in old(content);
    forall a, b: Lifetime | a in old(content) && b in old(content)
      ensures old(outlives(a, b)) ==> outlives(a, b)
    {
      if (old(outlives(a, b))) {
        var k: nat :| old(outlives#[k](a, b));
        FrameOutlivesHelper(a, b, running, k);
      }
    }
  }

  twostate lemma FrameOutlivesHelper(a: Lifetime, b: Lifetime, running: set<Thread>, k: nat)
    requires old(a in content && b in content && outlives#[k](a, b))
    requires old(content) <= content
    requires forall l: Lifetime | l in old(content) :: old(l.mightPointFrom) <= l.mightPointFrom && old(l.mightPointTo) <= l.mightPointTo
    ensures outlives#[k](a, b)
  {
    if (k > 0) {
      if (!old(a in b.mightPointTo)) {
        var x: Lifetime :| old(x in content && outlivesThrough#[k-1](a, x, b));
        FrameOutlivesHelper(a, x, running, k-2);
        FrameOutlivesHelper(x, b, running, k-2);
      }
    }
  }
}

method Havoc(ghost universe: Universe)
  requires universe.globalBaseInv()
  modifies universe, universe.content
  ensures universe.globalBaseInv() && universe.baseLegalTransitionsSequence()
{
  // Do nothing. Just havoc stuff on the caller side.
}

// Model the preemption of a given thread. Any other thread will have a chance to execute any number of legal transitions,
// modifying (1) volatile fiels of any object and (2) nonvolatile fields of objects that are not transitively owned by
// the preempting thread.
method Interference(ghost universe: Universe, ghost preempting: Thread)
  requires universe.globalInv() && preempting in universe.content
  modifies universe, universe.content
  ensures universe.globalInv()
  // Ensure that other threads executed any number of legal transitions.
  // Ensuring `globalInv2` would be wrong, because it's not guaranteed to be transitive.
  ensures universe.legalTransitionsSequence(set t: Thread | t in old(universe.content) && t != preempting)
{
  // This method could be bodyless. Checking the following implementation is just a consistency check.
  // The verifier will report errors in case `legalTransitionsSequence` is not transitive.
  var steps: int :| 0 <= steps;
  universe.sequenceLci({});
  while (steps > 0)
    invariant universe.globalInv()
    invariant universe.legalTransitionsSequence(set t: Thread | t in old(universe.content) && t != preempting)
    invariant universe.globalSequenceInv2()
  {
    // A thread of the environment (if there is any) executes a single legal transition.
    label preTransition:
    var envThreads: set<Thread> := set t: Thread | t in universe.content && t != preempting;
    assert universe.globalSequenceInv2(); // (1)
    Havoc(universe);
    if (|envThreads| > 0) {
      ghost var running: Thread :| running in envThreads;
      assume universe.legalTransition@preTransition(running);
      universe.lci@preTransition(running);
      assert universe.globalSequenceInv2@preTransition(); // (2)
      // We cannot call a 3-state lemma to apply the transitivity of `forall o: Object ... o.sequenceInv2`, so we have to assume this, checking (1) and (2).
      assume universe.baseLegalTransitionsSequence() ==> universe.globalSequenceInv2();
    } else {
      // No transition happens
      assume unchanged(universe) && unchanged(universe.content);
    }
    steps := steps - 1;
  }
}

method InterferenceWithFraming(ghost universe: Universe, ghost preempting: Thread)
  requires universe.globalInv() && preempting in universe.content
  modifies universe, universe.content
  ensures universe.globalInv()
  ensures universe.globalSequenceInv2()
  ensures universe.legalTransitionsSequence(set t: Thread | t in old(universe.content) && t != preempting)
  ensures forall a, b: Lifetime | a in old(universe.content) && b in old(universe.content) :: old(universe.outlives(a, b)) ==> universe.outlives(a, b)
{
  Interference(universe, preempting);
  universe.FrameOutlives();
  universe.sequenceLci(set t: Thread | t in old(universe.content));
}

datatype ObjectClassKind = Thread | OwnedObject | Lifetime

// A generic object trait
trait Object {
  // Universe of which the Object is a member.
  // This should really be a constant, but I don't know how to do that while factoring out join below,
  // because traits can't have constructors.
  ghost const universe: Universe

  // Global base invariant (from o's perspective)
  predicate objectGlobalBaseInv() reads * { this in universe.content && baseFieldsInv() && universe.globalBaseInv() }

  // Global invariant (from o's perspective) - I am in the universe and the universe is good. (This implies I am good also.)
  predicate objectGlobalInv() reads * { this in universe.content && universe.globalInv() }

  // Global 2-state invariant (from o's perspective).
  twostate predicate objectGlobalInv2() requires old(objectGlobalInv()) reads * { objectGlobalBaseInv() && universe.globalInv2() }

  predicate nonAliasing() reads this {
    && (objectClassKind() == Thread) == (this is Thread)
    && (objectClassKind() == OwnedObject) == (this is OwnedObject)
    && (objectClassKind() == Lifetime) == (this is Lifetime)
  }
  predicate triggerAxioms() reads this ensures triggerAxioms() {
    assume nonAliasing();
    nonAliasing()
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
  function objectClassKind(): ObjectClassKind // To prevent a class from extending both OwnedObject and Thread
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
  function objectClassKind(): ObjectClassKind { Thread }

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
    Havoc(universe);
    assume universe.baseLegalTransitionsSequence() && forall o: Object | o in old(universe.content) :: o.sequenceInv2();
    label mid:
    Havoc(universe);
    assume universe.baseLegalTransitionsSequence@mid() && forall o: Object | o in old@mid(universe.content) :: o.sequenceInv2@mid();
  }

  // Here we require a thread to create a thread. Programs shold assume that an initial thread exists in the universe.
  constructor(ghost universe: Universe, ghost running: Thread)
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
  // If the owner is `null`, this object is deallocated.
  ghost var owner: Object? // nonvolatile - The object that holds the write capability.

  ghost const lifetime: Lifetime // nonvolatile - The lifetime of this object.

  predicate alive() reads this`owner { this.owner != null }

  // To prevent a class from extending both OwnedObject and Thread
  function objectClassKind(): ObjectClassKind { OwnedObject }

  function objectFields(): set<Object> reads this {
    objectUserFields()
    + { lifetime }
    + (if (owner == null) then {} else { owner as Object })
  }

  predicate baseFieldsInv() reads this, universe {
    objectFields() <= universe.content
  }
  twostate lemma baseFieldsInvMonotonicity() requires old(baseFieldsInv()) && old(universe.content) <= universe.content && unchanged(this) ensures baseFieldsInv() {}

  twostate predicate unchangedNonvolatileFields() reads this {
    && old(owner) == owner
    && unchangedNonvolatileUserFields()
  }

  predicate localInv() reads * {
    && objectGlobalBaseInv()
    && this in lifetime.elements
    && (lifetime.alive() ==> owner != null)
    && (owner != null ==> localUserInv())
  }
  predicate inv() reads * ensures inv() ==> localInv() {
    && localInv()
    && (owner != null ==> userInv())
  }

  twostate predicate localInv2() reads * {
    && (owner != null ==> localUserInv2())
  }

  twostate predicate sequenceInv2() reads * {
    // Deallocated objects stay deallocated
    && (old(owner == null) ==> owner == null)
    // Optional feature: deallocated objects cannot change. This causes many qi instantiations.
    //&& (old(owner == null) ==> unchanged(this))
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
    && (old(owner) != null ==> userInv2())
    // When the owner changes, the invariant of the old and new owner must hold.
    && (old(owner) != owner ==>
      && old(owner).localInv()
      && old(owner).localInv2()
      && (owner != null ==>
        && owner.localInv()
        // In case the new owner existed in the old state
        && (var currOwner := owner; old(allocated(currOwner)) ==> owner.localInv2())
      )
    )
  }

  // Check transitivity of sequenceInv2()
  method CheckSequenceInv2()
    requires objectGlobalInv()
    modifies universe, universe.content
    ensures sequenceInv2()
  {
    Havoc(universe);
    assume universe.baseLegalTransitionsSequence() && forall o: Object | o in old(universe.content) :: o.sequenceInv2();
    var u1 := unchangedNonvolatileFields(); // (1)
    label mid:
    Havoc(universe);
    assume universe.baseLegalTransitionsSequence@mid() && forall o: Object | o in old@mid(universe.content) :: o.sequenceInv2@mid();
    var u2 := unchangedNonvolatileFields@mid(); // (2)
    // We cannot call a 3-state lemma to apply the transitivity of `unchangedNonvolatileFields`, so we have to assume it.
    assume u1 && u2 ==> unchangedNonvolatileFields();
  }

  // To be implemented in the class: 1-state invariant, 2-state invariant, admissibility proof...
  predicate volatileOwns() // If true, the set of owned objects can change without changing the nonvolatileVersion
  function objectUserFields(): set<Object> reads this
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
  //   Havoc(universe);
  //   assume unchangedNonvolatileFields();
  //   label mid:
  //   Havoc(universe);
  //   assume unchangedNonvolatileFields@mid();
  // }
}

function Bump(last: int): int ensures Bump(last) > last

class Lifetime extends Object {
  // All fields are nonvolatile
  ghost var owner: Thread?                // `null` if the lifetime is not alive.
  ghost var elements: set<OwnedObject>    // The objects that are part of this lifetime.
  ghost var mightPointTo: set<Lifetime>   // The lifetimes that can be pointed by the objects in this lifetime.
  ghost var mightPointFrom: set<Lifetime> // The lifetimes that might point to the objects in this lifetime.

  predicate unused() reads `mightPointFrom, `elements {
    mightPointFrom == {} && elements == {}
  }

  predicate alive() reads `owner {
    owner != null
  }

  predicate deallocable() reads this, mightPointFrom`owner, elements`owner {
    && (forall o: OwnedObject | o in elements :: !o.alive())
    && (forall l: Lifetime | l in mightPointFrom :: !l.alive())
  }

  // To prevent a class from extending 2 out of OwnedObject, Thread and Lifetime
  function objectClassKind(): ObjectClassKind { Lifetime }

  predicate baseFieldsInv() reads this, universe {
    && (owner != null ==> owner in universe.content)
    && elements <= universe.content
    && mightPointTo <= universe.content
    && mightPointFrom <= universe.content
  }
  twostate lemma baseFieldsInvMonotonicity() requires old(baseFieldsInv()) && old(universe.content) <= universe.content && unchanged(this) ensures baseFieldsInv() {}

  twostate predicate unchangedNonvolatileFields() reads this {
    && old(owner) == owner
    && old(elements) == elements
    && old(mightPointTo) == mightPointTo
    && old(mightPointFrom) == mightPointFrom
  }

  predicate localInv() reads * ensures localInv() ==> objectGlobalBaseInv() {
    && objectGlobalBaseInv()
    && (forall o: OwnedObject | o in elements :: o.lifetime == this)
    //&& (alive() ==> forall o: OwnedObject | o in elements :: o.alive()) // This is what Rust does. However,
    && (forall o: OwnedObject | o in elements :: o.alive() == alive())    // this allows to have shorter contracts. 
    && (alive() ==> forall l: Lifetime | l in mightPointTo :: l.alive())
    && (!alive() ==> forall l: Lifetime | l in mightPointFrom :: !l.alive())
    && (forall l: Lifetime | l in mightPointTo :: this in l.mightPointFrom)
    && (forall l: Lifetime | l in mightPointFrom :: this in l.mightPointTo)
  }
  predicate inv() reads * ensures inv() ==> localInv() { localInv() }

  twostate predicate sequenceInv2() reads * {
    && (old(!alive()) ==> !alive())
    && (owner != null ==> owner == old(owner)) // The owner cannot change
    && old(elements) <= elements
    && old(mightPointTo) <= mightPointTo
    && old(mightPointFrom) <= mightPointFrom
  }

  // Example that needs x.mightPointTo to grow:
  // x: Collection<'a>
  // x.add(&'b y) // <--

  twostate predicate localInv2() reads * { true }
  twostate predicate inv2() reads * ensures inv2() ==> localInv2() && sequenceInv2() { localInv2() && sequenceInv2() }

  twostate lemma sequenceAdmissibility(running: set<Thread>) requires goodPreAndLegalChangesSequence(running) ensures sequenceInv2() {}
  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {}

  // Lifetime
  constructor(ghost universe: Universe, ghost running: Thread, ghost owner: Thread, ghost mightPointTo: set<Lifetime>)
    requires universe.globalInv() && {running, owner} <= universe.content && mightPointTo <= universe.content
    requires forall l: Lifetime | l in mightPointTo :: l.owner == running
    modifies universe, mightPointTo`mightPointFrom
    ensures objectGlobalInv() && universe.legalTransition(running)
    ensures this.universe == universe && this.owner == owner
    ensures this.elements == {} && this.mightPointTo == mightPointTo && this.mightPointFrom == {}
    ensures universe.content == old(universe.content) + { this }
    ensures forall l: Lifetime | l in mightPointTo :: l.mightPointFrom == old(l.mightPointFrom) + { this }
  {
    this.universe := universe;
    this.owner := owner;
    this.elements := {};
    this.mightPointTo := mightPointTo;
    this.mightPointFrom := {};
    new;
    join();
    forall l: Lifetime | l in mightPointTo {
      l.mightPointFrom := l.mightPointFrom + { this };
    }
    universe.lci(running);
  }
}

// An owned integer type
class OwnedU32 extends OwnedObject {
  var value: int // nonvolatile

  predicate volatileOwns() { false }
  function objectUserFields(): set<Object> reads this { {} }

  twostate predicate unchangedNonvolatileUserFields() reads this {
    && old(value) == value
  }

  predicate localUserInv() reads * { true }
  predicate userInv() reads * ensures userInv() ==> localUserInv() { localUserInv() }
  twostate predicate localUserInv2() reads * { true }
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2() { localUserInv2() }

  twostate lemma sequenceAdmissibility(running: set<Thread>) requires goodPreAndLegalChangesSequence(running) ensures sequenceInv2() {}
  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {}

  constructor(ghost universe: Universe, ghost running: Thread, value: int)
    requires universe.globalInv() && running in universe.content
    modifies universe
    ensures objectGlobalInv() && universe.legalTransitionsSequence({running})
    ensures this.universe == universe && this.owner == running
    ensures this.value == value && this.lifetime.owner == running
    ensures universe.content == old(universe.content) + { this, this.lifetime }
    ensures this.lifetime.mightPointFrom == {} && this.lifetime.elements == { this }
  {
    label lci_l1:
    var lifetime := new Lifetime(universe, running, running, {});
    universe.FrameOutlives@lci_l1();
    universe.lci@lci_l1(running);
    assert {:split_here} true;

    label lci_l2:
    this.universe := universe;
    this.owner := running;
    this.lifetime := lifetime;
    this.value := value;
    new;
    join();
    lifetime.elements := { this };
    universe.FrameOutlives@lci_l2();
    universe.lci@lci_l2(running);
    assert {:split_here} true;
  }
}

// Lifetime `target` outlives lifetime `source`, which means that objects in `source` can point to objects in `target`.
class OutlivesClaim extends OwnedObject {
  ghost const target: Lifetime
  ghost const source: Lifetime

  predicate volatileOwns() { false }
  function objectUserFields(): set<Object> reads this { { source, target } }

  twostate predicate unchangedNonvolatileUserFields() reads this {
    true
  }

  predicate localUserInv() reads * {
    && objectGlobalBaseInv()
    && universe.outlives(target, source)
  }
  predicate userInv() reads * ensures userInv() ==> localUserInv() { localUserInv() }
  twostate predicate localUserInv2() reads * { true }
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2() { localUserInv2() }

  twostate lemma sequenceAdmissibility(running: set<Thread>) requires goodPreAndLegalChangesSequence(running) ensures sequenceInv2() {}
  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {
    universe.FrameOutlives();
  }

  lemma apply()
    requires objectGlobalInv() && owner != null
    ensures source.alive() ==> target.alive()
  {
    universe.OutlivesImpliesAlive();
  }

  predicate outlives(t: Lifetime, s: Lifetime) {
    target == t && source == s
  }

  predicate lifetimeOutlives(t: OwnedObject, s: OwnedObject) {
    target == t.lifetime && source == s.lifetime
  }

  // OutlivesClaim
  constructor(ghost universe: Universe, ghost running: Thread, ghost target: Lifetime, ghost source: Lifetime)
    requires universe.globalInv() && { running, target, source } <= universe.content
    requires target.owner == source.owner == running && universe.outlives(target, source)
    modifies universe, target`mightPointFrom, source`mightPointFrom
    ensures objectGlobalInv() && universe.legalTransitionsSequence({running})
    ensures this.universe == universe && this.owner == running
    ensures this.target == target && this.source == source
    ensures universe.content == old(universe.content) + { this, this.lifetime }
    ensures target.mightPointFrom == old(target.mightPointFrom) + { this.lifetime }
    ensures source.mightPointFrom == old(source.mightPointFrom) + { this.lifetime }
  {
    label lci_l1:
    //universe.OutlivesImpliesAlive();
    var lifetime := new Lifetime(universe, running, running, { target, source });
    universe.FrameOutlives@lci_l1();
    universe.lci@lci_l1(running);
    assert {:split_here} true;

    universe.OutlivesImpliesAlive();

    label lci_l2:
    this.universe := universe;
    this.owner := running;
    this.lifetime := lifetime;
    this.target := target;
    this.source := source;
    new;
    join();
    lifetime.elements := { this };
    universe.FrameOutlives@lci_l2();
    universe.lci@lci_l2(running);
    assert {:split_here} true;
  }
}

class Mutex extends OwnedObject {
  var data: OwnedU32 // volatile (it was UnsafeCell<u32>)
  var locked: bool // volatile (it was UnsafeCell<bool>)
  ghost var guards: set<MutexGuardU32> // volatile

  predicate volatileOwns() { true }
  function objectUserFields(): set<Object> reads this {
    guards + { data }
  }

  twostate predicate unchangedNonvolatileUserFields() reads this { true }

  predicate localUserInv() reads * {
    && lifetime == data.lifetime
    && (locked ==>
      && data.owner is MutexGuardU32
      && (
        var mutexGuard := data.owner as MutexGuardU32;
        && mutexGuard.owner != null
        && mutexGuard.mutex == this
        && guards == { mutexGuard }
      )
    )
    && (!locked ==>
      && data.owner == this
      && guards == {}
    )
  }
  predicate userInv() reads * ensures userInv() ==> localUserInv() {
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
    // All the following assertion are needed to trigger the appropriate quantifiers.
    universe.FrameOutlives();
    if (owner != null && locked) {
      var mutexGuard := data.owner as MutexGuardU32;
      assert mutexGuard.lifetime in old(universe.content);
    }
    assert unchanged(this);
    assert owner != null ==> userInv();
  }

  // Mutex
  constructor(ghost universe: Universe, ghost running: Thread, data: OwnedU32)
    requires universe.globalInv() && { running, data } <= universe.content && data.owner == running
    // TODO: Instead for the following `data.lifetime.owner == running` strong requirement, the constructor could
    // require a lifetime parameter `a` owned by running and such that `outlives(data.lifetime, a)` holds.
    // This is done with `mutexScope` in `MutexGuard`, where the lifetime of the mutex cannot be owned by `running`.
    requires data.lifetime.owner == running
    modifies universe, data, data.lifetime`elements
    ensures objectGlobalInv() && universe.legalTransition(running) // This could be legalTransitionsSequenceAnyThread
    ensures this.universe == universe && this.owner == running
    ensures this.lifetime == data.lifetime
    ensures this.data == data && !this.locked
    ensures universe.content == old(universe.content) + { this }
    ensures data.lifetime.elements == old(data.lifetime.elements) + { this }
  {
    this.universe := universe;
    this.owner := running;
    this.lifetime := data.lifetime;
    this.data := data;
    this.locked := false;
    this.guards := {};
    new;
    join();
    data.lifetime.elements := data.lifetime.elements + { this };
    this.data.owner := this;
    this.data.nonvolatileVersion := Bump(this.data.nonvolatileVersion);
    assert this.inv();
    assert this.data.inv();
    universe.FrameOutlives();
    universe.lci(running);
    assert {:split_here} true;
  }
}

class MutexGuardU32 extends OwnedObject {
  var mutex: Mutex // nonvolatile
  ghost var data: OwnedU32 // nonvolatile

  predicate volatileOwns() { false }
  function objectUserFields(): set<Object> reads this {
    { mutex, data }
  }

  twostate predicate unchangedNonvolatileUserFields() reads this {
    && old(mutex) == mutex
    && old(data) == data
  }

  predicate localUserInv() reads * {
    // TODO: Instead of the following `.. <= universe.content`, we could add `objectGlobalInv` to the precondition of all invariants.
    && { this.lifetime, mutex.lifetime } <= universe.content
    // TODO: As an alternative, Mutex could enforce that `forall g in guards :: g.localInv()` even when the Mutex is deallocated.
    // This could be done by adding a new `deallocationUserInv()` to OwnedObject. It's probably easier to verify.
    && universe.outlives(mutex.lifetime, this.lifetime)
    && mutex.owner != null
    && mutex.locked
    && mutex.guards == { this }
    && mutex.data.owner == this
    && mutex.data == data
  }
  predicate userInv() reads * ensures userInv() ==> localUserInv() {
    && localUserInv()
    && mutex.localInv()
  }
  twostate predicate localUserInv2() reads * {
    && old(mutex) == mutex
  }
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2() {
    && localUserInv2()
    && mutex.localInv2()
    // We can express what should happen during deallocation
    && (owner == null ==> mutex.localInv())
  }

  twostate lemma sequenceAdmissibility(running: set<Thread>) requires goodPreAndLegalChangesSequence(running) ensures sequenceInv2() {}
  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {
    universe.FrameOutlives(); // Alternativelly, this object should store an OutlivesClaim.
  }

  // MutexGuardU32
  constructor {:vcs_split_on_every_assert} (ghost universe: Universe, ghost running: Thread, ghost scope: Lifetime, mutex: Mutex, ghost mutexScope: Lifetime)
    requires universe.globalInv() && { running, scope, mutex, mutexScope } <= universe.content
    requires scope.owner == running && mutexScope.owner == running && scope != mutexScope
    requires universe.outlives(mutex.lifetime, mutexScope) && universe.outlives(mutexScope, scope) && scope.unused();
    requires !mutex.locked
    // The user should be able to remove objects owned by the running thread from the modifies clause
    modifies universe, universe.content - (set l: Lifetime | l in universe.content && l.owner == running) + {scope, mutexScope}
    // ensures universe.legalTransitionsSequence(running) would be more precise and more complete
    ensures objectGlobalInv() && universe.legalTransitionsSequence({running}) // This could be legalTransitionsSequenceAnyThread()
    ensures this.universe == universe && this.owner == running
    ensures this.mutex == mutex && this.data == mutex.data && this.mutex.locked && this.mutex.data.owner == this
    ensures this.lifetime.mightPointFrom == {} && this.lifetime.elements == { this } && this.lifetime.owner == running
    ensures mutexScope.mightPointFrom == old(mutexScope.mightPointFrom) + { this.lifetime }
    ensures { this } <= universe.content
    ensures !scope.alive()
  {
    // TODO: This constructor does not call `universe.Interference`, but it could if `!mutex.locked` were ensured
    // by a claim passed by parameter.

    // Creating lifetimes is atomic, because they are ghost objects.
    label lci_l1:
    var lifetime := new Lifetime(universe, running, running, { mutexScope });
    universe.FrameOutlives@lci_l1();
    universe.lci@lci_l1(running);
    assert {:split_here} true;

    universe.OutlivesImpliesAlive();

    label lci_l2:
    this.universe := universe;
    this.owner := running;
    this.lifetime := lifetime;
    this.mutex := mutex;
    this.data := mutex.data;
    new;
    join();
    lifetime.elements := lifetime.elements + { this };
    // Acquire the lock
    this.mutex.locked := true;
    this.mutex.guards := { this };
    // Transfer ownership of `this.mutex.data` from `this.mutex` to `this`.
    this.mutex.data.owner := this;
    this.mutex.data.nonvolatileVersion := Bump(this.mutex.data.nonvolatileVersion);
    // We don't need to bump this.mutex.nonvolatileVersion, because it uses volatileOwns.
    universe.FrameOutlives@lci_l2();
    assert universe.outlives(mutex.lifetime, mutexScope) && universe.outlives(mutexScope, this.lifetime); // needed
    assert universe.outlives(mutex.lifetime, this.lifetime); // needed
    assert lifetime.alive(); // helps dafny
    assert mutex.owner != null; // helps dafny
    assert this.localUserInv();
    assert this.userInv();
    assert this.inv();
    assert this.mutex.inv();
    assert this.mutex.data.inv();
    universe.lci@lci_l2(running);
    assert {:split_here} true;

    label lci_l3:
    scope.owner := null;
    universe.FrameOutlives@lci_l3();
    universe.lci@lci_l3(running);
    assert {:split_here} true;
  }
}
