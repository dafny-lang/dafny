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
  var content: set<Object>

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

  // Global 2-state invariant: all old objects satisfy their 2-state invariants and basic properties of legal transitions.
  twostate predicate globalInv2() reads * {
    && (forall o: Object | o in old(content) :: o in content && o.inv2())
    // The following could be `legalTransition`, but it's unnecessarily strong. `baseLegalTransitionsSequence` is enough.
    && baseLegalTransitionsSequence()
  }

  // This transitive relation describes basic properties of sequences of legal transitions.
  // This relation does not mention the invariants of the objects. For that, see the `legalTransition` predicate.
  twostate predicate baseLegalTransitionsSequence() reads * {
    // The universe only grows
    && old(content) <= content
    // All objects added to the universe weren't allocated in the old state.
    // This allows to satisfy the modifies clause checks on the caller side in a sequence of methods that might
    // modify the universe. For example, the `Havoc` and `Interference` methods.
    && (forall o: Object | o !in old(content) && o in content :: !old(allocated(o)))
    // Version numbers only increase
    && (forall o: OwnedObject | o in old(content):: old(o.nonvolatileVersion) <= o.nonvolatileVersion)
  }

  // This relation describes a sequence of legal transitions, each of which can be performed by a newly created thread
  // or by one of the threads in the `running` parameter.
  // This definition is weaker than `legalTransition`, but it's transitive (if it holds for A->B and B->C then it holds also for A->C).
  // This definition is also monotonic w.r.t. `running`: `legalTransitionsSequence(S)` should imply `legalTransitionsSequence(T)` whenever `S <= T`.
  // This definition is needed in the definition of the `Interference` and `Havoc` methods, and in the loop invariants of the `Run` methods.
  twostate predicate legalTransitionsSequence(running: set<Thread>) reads * {
    && baseLegalTransitionsSequence()
    && old(globalBaseInv())
    && globalBaseInv()
    // Old objects must obey their transitive 2-state invariants.
    // `transitiveInv2` needs to be transitive under the assumption `baseLegalTransitionsSequence`.
    && (forall o: Object | o in old(content) :: o.transitiveInv2())
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
    && globalBaseInv()
    // The first condition for legality: old objects that change a field must obey their 1- and 2-state invariants.
    && (forall o: Object | o in old(content) :: unchanged(o) || (o.inv() && o.inv2()))
    // The second condition for legality: new objects must satisfy their invariants.
    && (forall o: Object | o in content && o !in old(content) :: o.inv())
  }

  // LCI soundness: legal transitions are good. This makes use of the admissibility obligations build into Object's.
  // The `TypingAxiom3(running)` and `ProveTransitiveInv2` lemmas are often useful to prove the precondition.
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
    // Ensuring `globalInv2` would be wrong, because it's not guaranteed to be transitive
    // Ensure that other threads executed any number of legal transitions
    ensures legalTransitionsSequence(set t: Thread | t in old(content) && t != preempting)
  {
    // This method could be bodyless. Checking the following implementation is just a consistency check.
    // The verifier will report errors in case `legalTransitionsSequence` is not transitive.
    var steps: int :| 0 <= steps;
    ProveReflexiveLegalTransitionsSequence(set t: Thread | t in content && t != preempting);
    while (steps > 0)
      invariant globalInv() && legalTransitionsSequence(set t: Thread | t in old(content) && t != preempting)
    {
      // A thread of the environment (if there is any) executes a single legal transition.
      var envThreads: set<Thread> := set t: Thread | t in content && t != preempting;
      if (|envThreads| > 0) {
        ghost var running: Thread :| running in envThreads;
        label preTransition:
        assert forall o: Object | o in old(content) :: o.transitiveInv2(); // (1)
        Havoc();
        assume legalTransition@preTransition(running);
        ProveTransitiveInv2@preTransition();
        lci@preTransition(running);
        assert forall o: Object | o in old@preTransition(content) :: o.transitiveInv2@preTransition(); // (2)
        // We cannot call a 3-state lemma to apply the transitivity of `transitiveInv2`, so we have to assume this, checking (1) and (2).
        assume baseLegalTransitionsSequence() ==> forall o: Object | o in old(content) :: o.transitiveInv2();
      }
      steps := steps - 1;
    }
  }

  // A helper lemma, to be used before the `lci` lemma to prove that a transition only changed nonvolatile fields when allowed by the owner.
  // TODO: See if this can be merged into `lci` or some 2-state invariant.
  twostate lemma ProveTransitiveInv2()
    ensures forall o: Object | o in old(content) ::
      (o is OwnedObject ==>
        && unchanged(o)
        && (forall x: OwnedObject | x in old(o.universe.content) && old(x.owner) == o :: old(x.nonvolatileVersion) == x.nonvolatileVersion && x.owner == o)
      ) ==> o.transitiveInv2()
  {
    forall o: Object | o in old(content) ensures
      (o is OwnedObject ==>
        && unchanged(o)
        && (forall x: OwnedObject | x in old(o.universe.content) && old(x.owner) == o :: old(x.nonvolatileVersion) == x.nonvolatileVersion && x.owner == o)
      ) ==> o.transitiveInv2()
    {
      if (o is OwnedObject) {
        var ownedObject := o as OwnedObject;
        if (unchanged(o) && forall x: OwnedObject | x in old(ownedObject.universe.content) && old(x.owner) == ownedObject :: old(x.nonvolatileVersion) == x.nonvolatileVersion && x.owner == ownedObject) {
          ownedObject.ProveUnchangedNonvolatileFields();
        }
      } else {
        TypingAxiom5(o);
      }
    }
  }

  // Consistency check: baseLegalTransitionsSequence should be reflexive.
  lemma ProveReflexiveBaseLegalTransitionsSequence() ensures baseLegalTransitionsSequence() {}

  // Consistency check: baseLegalTransitionsSequence should be transitive.
  method CheckTransitiveBaseLegalTransitionsSequence()
    requires globalBaseInv()
    modifies this, content
    ensures baseLegalTransitionsSequence()
  {
    Havoc();
    Havoc();
  }

  // Consistency check: assuming globalBaseInv, legalTransitionsSequence should be reflexive.
  lemma ProveReflexiveLegalTransitionsSequence(running: set<Thread>) ensures globalBaseInv() ==> legalTransitionsSequence(running) {
    forall o: Object | o in old(content) ensures o.transitiveInv2() {
      o.ProveReflexiveTransitiveInv2();
    }
  }

  // Consistency check: legalTransitionsSequence should be transitive.
  method CheckTransitiveLegalTransitionsSequence(running: set<Thread>)
    requires globalInv()
    modifies this, content
    ensures legalTransitionsSequence(running)
  {
    Havoc();
    assume legalTransitionsSequence(running);
    assert forall o: Object | o in old(content) :: o.transitiveInv2(); // (1)
    label mid:
    Havoc();
    assume legalTransitionsSequence@mid(running);
    assert forall o: Object | o in old@mid(content) :: o.transitiveInv2@mid(); // (2)
    // We cannot call a 3-state lemma to apply the transitivity of `transitiveInv2`, so we have to assume it, checking (1) and (2).
    assume baseLegalTransitionsSequence() ==> forall o: Object | o in old(content) :: o.transitiveInv2();
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
trait Object extends object {
  // Universe of which the Object is a member.
  // This should really be a constant, but I don't know how to do that while factoring out join below,
  // because traits can't have constructors.
  const universe: Universe

  // Base invariant: we're in the universe, and the universe satisfies its base.
  ghost predicate baseInv() reads * { this in universe.content && universe.globalBaseInv() }

  // Join the universe
  method join()
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
    && old(baseInv() && universe.globalInv()) && baseInv() // TODO: this could just be `this in universe.content`. legalTransition implies the rest.
    && unchanged(this)
    && universe.legalTransition(running)
  }

  // Global invariant (from o's perspective) - I am in the universe and the universe is good. (This implies I am good also.)
  ghost predicate objectGlobalInv() reads * { baseInv() && universe.globalInv() }

  // Global 2-state invariant (from o's perspective).
  twostate predicate objectGlobalInv2() requires old(objectGlobalInv()) reads * { baseInv() && universe.globalInv2() }

  // To be implemented: 1-state invariant, 2-state invariant, admissibility proof...
  ghost predicate isOwnedObject() // To prevent a class from extending both OwnedObject and Thread
  ghost predicate localInv() reads *
  twostate predicate localInv2() reads *
  ghost predicate inv() ensures inv() ==> localInv() reads *
  twostate predicate transitiveInv2() reads * // Assuming universe.baseLegalTransitionsSequence(), this should be transitive. This can be checked in the classes. See `CheckTransitiveInv2` below.
  twostate predicate inv2() ensures inv2() ==> localInv2() && transitiveInv2() reads *
  lemma ProveReflexiveTransitiveInv2() ensures transitiveInv2()
  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv()
}

class Thread extends Object {
  // To prevent a class from extending both OwnedObject and Thread
  ghost predicate isOwnedObject() { false }

  ghost predicate localInv() reads * {
    && baseInv()
  }
  ghost predicate inv() reads * ensures inv() ==> localInv() {
    && localInv()
  }

  twostate predicate localInv2() reads * {
    true
  }
  twostate predicate transitiveInv2() reads * {
    true
  }
  twostate predicate inv2() reads * ensures inv2() ==> localInv2() && transitiveInv2() {
    localInv2() && transitiveInv2()
  }

  lemma ProveReflexiveTransitiveInv2() ensures transitiveInv2()

  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {}

  // Here we require a thread to create a thread. Programs shold assume that an initial thread exists in the universe.
  constructor(universe: Universe, ghost running: Thread)
    requires universe.globalInv() && running in universe.content
    modifies universe
    ensures objectGlobalInv() && universe.globalInv2()
  {
    this.universe := universe;
    new;
    TypingAxiom3(this);
    join();
    universe.ProveTransitiveInv2();
    universe.lci(running);
  }
}

trait OwnedObject extends Object {
  ghost var nonvolatileVersion: int
  ghost var owner: Object // nonvolatile

  // To prevent a class from extending both OwnedObject and Thread
  ghost predicate isOwnedObject() { true }

  ghost predicate localInv() reads * {
    && baseInv()
    && owner in universe.content
    && baseUserInv()
    && localUserInv()
  }
  ghost predicate inv() reads * ensures inv() ==> localInv() {
    && localInv()
    && userInv()
  }

  twostate predicate localInv2() reads * {
    && localUserInv2()
  }

  // Assuming `universe.globalBaseInv2()`, this relation should be transitive.
  twostate predicate transitiveInv2() reads * {
    && (old(nonvolatileVersion) == nonvolatileVersion ==>
      // Nonvolatile fields are only allowed to change when the nonvolatileVersion changes.
      // (The ProveTransitiveInv2 lemma should be useful to prove this.)
      && unchangedNonvolatileFields()
      // Transitivity: if a nonvolatileVersion doesn't change, the same should apply to all owned objects
      && (forall o: OwnedObject | o in old(universe.content) && old(o.owner) == this :: old(o.nonvolatileVersion) == o.nonvolatileVersion && o.owner == this)
    )
    && (old(owner) is OwnedObject ==>
      var oldOwner := old(owner) as OwnedObject;
      // The nonvolatileVersion cannot change if the version of the old owner doesn't change.
      old(oldOwner.nonvolatileVersion) == oldOwner.nonvolatileVersion ==> old(nonvolatileVersion) == nonvolatileVersion
    )
  }
  twostate predicate inv2() reads * ensures inv2() ==> localInv2() && transitiveInv2() {
    && localInv2()
    && transitiveInv2()
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

  lemma ProveReflexiveTransitiveInv2() ensures transitiveInv2() {
    ProveUnchangedNonvolatileFields();
  }

  twostate predicate unchangedNonvolatileFields() reads this {
    old(owner) == owner && unchangedNonvolatileUserFields()
  }
  twostate lemma ProveUnchangedNonvolatileFields() requires unchanged(this) ensures unchangedNonvolatileFields() {
    ProveUnchangedNonvolatileUserFields();
  }

  // To be implemented in the class: 1-state invariant, 2-state invariant, admissibility proof...
  twostate predicate unchangedNonvolatileUserFields() reads this // Checking transitivity is up to the classes that implement this trait.
  ghost predicate baseUserInv() reads *
  ghost predicate localUserInv() reads *
  twostate predicate localUserInv2() reads *
  ghost predicate userInv() reads * ensures userInv() ==> localUserInv()
  twostate predicate userInv2() reads * ensures userInv2() ==> localUserInv2()
  twostate lemma ProveUnchangedNonvolatileUserFields() requires unchanged(this) ensures unchangedNonvolatileUserFields()

  // Every class should check the transitivity of transitiveInv2():
  // method CheckTransitiveInv2()
  //   requires objectGlobalInv()
  //   modifies universe, universe.content
  //   ensures transitiveInv2()
  // {
  //   universe.Havoc();
  //   assume transitiveInv2() && universe.baseLegalTransitionsSequence();
  //   label mid:
  //   universe.Havoc();
  //   assume transitiveInv2@mid() && universe.baseLegalTransitionsSequence@mid();
  //   universe.ProveTransitiveInv2();
  // }
}

method BumpVersion(ghost last: int) returns (res: int) ensures res > last

// Axioms: Instances of OwnedObject cannot alias instances of Thread.
// This is to workaround an incompleteness of Dafny, which doesn't know that classes don't alias instances of traits that the class doesn't extend.
// I asked on Slack if there is a way to assume these globally.
lemma TypingAxiom1(universe: Universe)
  ensures forall a: Thread, b: OwnedObject | a in universe.content && b in universe.content :: a as Object != b
lemma TypingAxiom2(universe: Universe, a: Thread)
  ensures forall b: OwnedObject | b in universe.content :: a as object != b
lemma TypingAxiom3(a: Thread)
  ensures !((a as Object) is OwnedObject)
lemma TypingAxiom4(b: OwnedObject)
  ensures !((b as Object) is Thread)
lemma TypingAxiom5(a: Object)
  ensures (a is OwnedObject) || (a is Thread)

// An example of type without fields
class EmptyType extends OwnedObject {
  twostate predicate unchangedNonvolatileUserFields() reads this {
    true
  }
  twostate lemma ProveUnchangedNonvolatileUserFields() requires unchanged(this) ensures unchangedNonvolatileUserFields() {}

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

  // Check transitivity of transitiveInv2()
  method CheckTransitiveInv2()
    requires objectGlobalInv()
    modifies universe, universe.content
    ensures transitiveInv2()
  {
    universe.Havoc();
    assume transitiveInv2() && universe.baseLegalTransitionsSequence();
    label mid:
    universe.Havoc();
    assume transitiveInv2@mid() && universe.baseLegalTransitionsSequence@mid();
    universe.ProveTransitiveInv2();
  }

  constructor(universe: Universe, ghost running: Thread)
    requires universe.globalInv() && running in universe.content
    modifies universe
    ensures objectGlobalInv() && universe.globalInv2()
    // The following might not always be needed
    ensures this.universe == universe && this.owner == running
    ensures universe.content == old(universe.content) + { this }
  {
    this.universe := universe;
    this.owner := running;
    new;
    join();
    universe.ProveTransitiveInv2();
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
  twostate lemma ProveUnchangedNonvolatileUserFields() requires unchanged(this) ensures unchangedNonvolatileUserFields() {}

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

  // Check transitivity of transitiveInv2()
  method CheckTransitiveInv2()
    requires objectGlobalInv()
    modifies universe, universe.content
    ensures transitiveInv2()
  {
    universe.Havoc();
    assume transitiveInv2() && universe.baseLegalTransitionsSequence();
    label mid:
    universe.Havoc();
    assume transitiveInv2@mid() && universe.baseLegalTransitionsSequence@mid();
    universe.ProveTransitiveInv2();
  }

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
    universe.ProveTransitiveInv2();
    TypingAxiom3(running);
    universe.lci(running);
  }
}

class Remaining extends OwnedObject {
  var value: int // nonvolatile

  twostate predicate unchangedNonvolatileUserFields() reads this {
    && old(value) == value
  }
  twostate lemma ProveUnchangedNonvolatileUserFields() requires unchanged(this) ensures unchangedNonvolatileUserFields() {}

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

  // Check transitivity of transitiveInv2()
  method CheckTransitiveInv2()
    requires objectGlobalInv()
    modifies universe, universe.content
    ensures transitiveInv2()
  {
    universe.Havoc();
    assume transitiveInv2() && universe.baseLegalTransitionsSequence();
    label mid:
    universe.Havoc();
    assume transitiveInv2@mid() && universe.baseLegalTransitionsSequence@mid();
    universe.ProveTransitiveInv2();
  }

  constructor(universe: Universe, ghost running: Thread, initialValue: int)
    requires universe.globalInv() && running in universe.content
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
    universe.ProveTransitiveInv2();
    TypingAxiom3(running);
    universe.lci(running);
  }
}

// fn incrementer(counter: Arc<AtomicIsize>, remaining: Box<isize>)
//   requires remaining.data == 10
//   ensures remaining.data == 0
// {
//            // 0: inv_pre: remaining.data == 10
//   let mut i = 0;
//            // 1: inv_pre: 0 <= i <= 10 && remaining.data == 10
//   while i < 10 {
//     label l2:
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
//     *remaining -= 1;
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
  twostate lemma ProveUnchangedNonvolatileUserFields() requires unchanged(this) ensures unchangedNonvolatileUserFields() {}

  ghost predicate baseUserInv() reads * {
    && counter in universe.content
    && remaining in universe.content
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
  }

  twostate lemma admissibility(running: Thread) requires goodPreAndLegalChanges(running) ensures inv2() && inv() {}

  // Check transitivity of transitiveInv2()
  method CheckTransitiveInv2()
    requires objectGlobalInv()
    modifies universe, universe.content
    ensures transitiveInv2()
  {
    universe.Havoc();
    assume transitiveInv2() && universe.baseLegalTransitionsSequence();
    label mid:
    universe.Havoc();
    assume transitiveInv2@mid() && universe.baseLegalTransitionsSequence@mid();
    universe.ProveTransitiveInv2();
  }

  constructor(universe: Universe, ghost running: Thread, counter: AtomicCounter, remaining: Remaining)
    requires universe.globalInv() && running in universe.content && counter in universe.content && remaining in universe.content
    requires remaining.owner == running && remaining.value == 10 // The precondition
    modifies universe, remaining
    ensures objectGlobalInv() && universe.globalInv2()
    // The following might not always be needed
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
    universe.ProveTransitiveInv2();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Run(running: Thread)
    requires this.objectGlobalInv() && running in universe.content && this.owner == running && programCounter == 0
    modifies universe, universe.content, running, this, this.counter, this.remaining
    ensures this.objectGlobalInv() && programCounter == 10
    decreases *
  {
    // The precondition is required and ensured by the constructor
    universe.Interference(running);

    Statement0(running);
    universe.Interference(running);

    Statement1(running);
    universe.Interference(running);
    
    label beforeLoop:
    while (programCounter == 2)
      invariant this.objectGlobalInv() && running in universe.content && this.owner == running && (programCounter == 2 || programCounter == 9)
      invariant universe.baseLegalTransitionsSequence@beforeLoop()
      //invariant universe.legalTransitionsSequence@beforeLoop(set t: Thread | t in old@beforeLoop(universe.content)) // TODO: Needed to prove termination
      modifies universe, universe.content, running, this, this.counter, this.remaining
      decreases * // TODO: To prove termination, we need to add user properties to transitiveInv2 and add legalTransitionsSequence@beforeLoop to the loop invariant.
    {
      // Dafny's verification time is apparently cubic (R^2 = 0.9995) in the number of method calls, so we help
      // Dafny by wrapping sequences of calls in separate methods. This can be some as many times as needed, even
      // ending up with a binary-tree-like call graph to minimize the number of calls done in each method.
      RunLoopBody(running);
    }

    Statement9(running);
    universe.Interference(running);

    Statement10(running); // Internally, this checks the postcondition
  }

  method RunLoopBody(running: Thread)
    requires this.objectGlobalInv() && running in universe.content && this.owner == running && programCounter == 2
    modifies universe, universe.content, running, this, this.counter, this.remaining
    ensures this.objectGlobalInv() && this.owner == running && (programCounter == 2 || programCounter == 9)
    ensures universe.baseLegalTransitionsSequence()
    //ensures universe.legalTransitionsSequence(set t: Thread | t in old(universe.content)) // TODO: Needed to prove termination
  {
    universe.Interference(running);

    Statement2(running);
    universe.Interference(running);

    Statement3(running);
    universe.Interference(running);

    Statement4(running);
    universe.Interference(running);

    Statement5(running);
    universe.Interference(running);

    Statement6(running);
    universe.Interference(running);

    Statement7(running);
    universe.Interference(running);

    Statement8(running);
    universe.Interference(running);
  }

  method Statement0(ghost running: Thread)
    requires this.objectGlobalInv() && running in universe.content && this.owner == running && programCounter == 0
    modifies this
    ensures this.objectGlobalInv() && universe.globalInv2() && programCounter == 1
    ensures universe.legalTransition(running)
  {
    i := 0;
    programCounter := 1;
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.ProveTransitiveInv2();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement1(ghost running: Thread)
    requires this.objectGlobalInv() && running in universe.content && this.owner == running && programCounter == 1
    modifies this
    ensures this.objectGlobalInv() && universe.globalInv2() && (programCounter == 2 || programCounter == 9)
    ensures universe.legalTransition(running)
  {
    if (i < 10) { programCounter := 2; } else { programCounter := 9; }
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.ProveTransitiveInv2();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement2(ghost running: Thread)
    requires this.objectGlobalInv() && running in universe.content && this.owner == running && programCounter == 2
    modifies this
    ensures this.objectGlobalInv() && universe.globalInv2() && programCounter == 3
    ensures universe.legalTransition(running)
  {
    initial_value := counter.value;
    programCounter := 3;
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.ProveTransitiveInv2();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement3(ghost running: Thread)
    requires this.objectGlobalInv() && running in universe.content && this.owner == running && programCounter == 3
    modifies this, counter
    ensures this.objectGlobalInv() && universe.globalInv2() && programCounter == 4
    ensures universe.legalTransition(running)
  {
    counter.value := counter.value + 1;
    programCounter := 4;
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.ProveTransitiveInv2();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement4(ghost running: Thread)
    requires this.objectGlobalInv() && running in universe.content && this.owner == running && programCounter == 4
    modifies this
    ensures this.objectGlobalInv() && universe.globalInv2() && programCounter == 5
    ensures universe.legalTransition(running)
  {
    final_value := counter.value;
    programCounter := 5;
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.ProveTransitiveInv2();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement5(ghost running: Thread)
    requires this.objectGlobalInv() && running in universe.content && this.owner == running && programCounter == 5
    modifies this
    ensures this.objectGlobalInv() && universe.globalInv2() && programCounter == 6
    ensures universe.legalTransition(running)
  {
    assert initial_value + 1 <= final_value;
    programCounter := 6;
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.ProveTransitiveInv2();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement6(ghost running: Thread)
    requires this.objectGlobalInv() && running in universe.content && this.owner == running && programCounter == 6
    modifies this
    ensures this.objectGlobalInv() && universe.globalInv2() && programCounter == 7
    ensures universe.legalTransition(running)
  {
    i := i + 1;
    programCounter := 7;
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.ProveTransitiveInv2();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement7(ghost running: Thread)
    requires this.objectGlobalInv() && running in universe.content && this.owner == running && programCounter == 7
    modifies this, remaining
    ensures this.objectGlobalInv() && universe.globalInv2() && this.owner == running && programCounter == 8
    ensures universe.legalTransition(running)
  {
    remaining.value := remaining.value - 1;
    remaining.nonvolatileVersion := BumpVersion(remaining.nonvolatileVersion);
    programCounter := 8;
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.ProveTransitiveInv2();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement8(ghost running: Thread)
    requires this.objectGlobalInv() && running in universe.content && this.owner == running && programCounter == 8
    modifies this
    ensures this.objectGlobalInv() && universe.globalInv2() && (programCounter == 2 || programCounter == 9)
    ensures universe.legalTransition(running)
  {
    if (i < 10) { programCounter := 2; } else { programCounter := 9; }
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.ProveTransitiveInv2();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement9(ghost running: Thread)
    requires this.objectGlobalInv() && running in universe.content && this.owner == running && programCounter == 9
    modifies this
    ensures this.objectGlobalInv() && universe.globalInv2() && programCounter == 10
    ensures universe.legalTransition(running)
  {
    assert i == 10;
    programCounter := 10;
    nonvolatileVersion := BumpVersion(nonvolatileVersion);
    universe.ProveTransitiveInv2();
    TypingAxiom3(running);
    universe.lci(running);
  }

  method Statement10(ghost running: Thread)
    requires this.objectGlobalInv() && running in universe.content && this.owner == running && programCounter == 10
    ensures this.objectGlobalInv() && universe.globalInv2() && programCounter == 10
    ensures universe.legalTransition(running)
  {
    assert remaining.value == 0;
    universe.ProveTransitiveInv2();
    TypingAxiom3(running);
    universe.lci(running);
  }
}
