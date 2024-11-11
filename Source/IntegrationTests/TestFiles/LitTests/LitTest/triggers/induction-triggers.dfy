// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s" -- --show-hints

predicate f(n: nat) { if n == 0 then true else f(n-1) }
predicate g(n: nat) { false }

// Default: auto-generated trigger ⇒ Proof passes.
lemma Default(n: nat) ensures f(n) {}

// Manual list of variables ⇒ Proof passes.
lemma {:induction n} ListOfVars(n: nat) ensures f(n) {}

// No induction ⇒ Proof fails.
lemma {:induction false} NoInduction(n: nat) ensures f(n) {} // error

// No induction, with manual proof ⇒ Proof passes.
lemma {:induction false} ManualInduction(n: nat)
  ensures f(n)
{
  forall ih_n: nat | (n decreases to ih_n) {
    ManualInduction(ih_n);
  }
}

// No triggers, so no auto induction ⇒ Proof fails.
lemma NoTriggers(n: nat) ensures f(n + 0) {} // error

// No triggers but forced induction, so warning ⇒ Proof passes.
lemma {:induction} InductionWarning(n: nat) ensures f(n + 0) {}

// Explicit triggers, so no warning ⇒ Proof passes.
lemma {:induction} {:inductionTrigger f(n)} NoWarning2(n: nat) ensures f(n + 0) {}

// Legacy mode: auto induction with no triggers ⇒ Proof passes.
lemma {:inductionTrigger} Legacy(n: nat) ensures f(n) {}
lemma {:inductionTrigger} Legacy1(n: nat) ensures f(n + 0) {}
lemma {:induction} {:inductionTrigger} Legacy2(n: nat) ensures f(n + 0) {}

// Poorly chosen explicit trigger, so no warning ⇒ Proof fails.
lemma {:induction} {:inductionTrigger g(n)} NoWarning3(n: nat) ensures f(n + 0) {} // error

// No triggers but forced induction with a given variable list, so warning ⇒ Proof passes.
lemma {:induction n} InductionWarningN(n: nat) ensures f(n + 0) {}
