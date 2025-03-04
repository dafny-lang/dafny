// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s" -- --show-hints

module SuchThat {
  predicate Q(x: int)
  function F(x: int): int

  method TestSuchThat()
    requires Q(18)
  {
    // In the following lines, the trigger {Q(_)} is selected automatically
    if
    case true =>
      assert exists w :: Q(w); // trigger: Q{w}
    case true =>
      assert var y :| Q(y); F(y) == F(y); // trigger: Q{y}
    case true =>
      var z :| Q(z); // trigger: Q{z}
  }

  method NothingToTriggerOn() {
    // In the following lines, there is no good trigger, so a warning is generated
    if
    case true =>
      assert exists w :: Q(w + 1); // warning: no trigger; error: assertion failure
    case true =>
      assert var y :| Q(y + 1); F(y) == F(y); // error: cannot find witness (with no-trigger hint)
    case true =>
      var z :| Q(z + 2); // warning: no trigger; error: cannot find witnes (with no-trigger hint)
  }

  method NoWarn() {
    // The :nowarn attribute replacing the no-trigger warning by an informational message
    if
    case true =>
      assert exists w {:nowarn} :: Q(w + 1); // info: no trigger; error: assertion failure
    case true =>
      assert var y {:nowarn} :| Q(y + 1); F(y) == F(y); // error: cannot find witness (with no-trigger hint -- this hint is impervious to :nowarn)
    case true =>
      var z {:nowarn} :| Q(z + 2); // error: info: no trigger; cannot find witness (with no-trigger hint)
  }

  method ManualTriggerThatWorks()
    requires F(10) == 20
    requires Q(11)
  {
    // The following lines use the manually specific trigger
    if
    case true =>
      assert exists w {:trigger F(w)} :: Q(w + 1);
    case true =>
      assert var y {:trigger F(y)} :| Q(y + 1); F(y) == F(y);
    case true =>
      var z {:trigger F(z)} :| Q(z + 1);
  }

  method ManualTriggerThatDoesNotWork()
    requires F(11) == 20
    requires Q(11)
  {
    // The following lines use the manually specific trigger
    if
    case true =>
      assert exists w {:trigger F(w)} :: Q(w + 1); // error: assertion failure
    case true =>
      assert var y {:trigger F(y)} :| Q(y + 1); F(y) == F(y); // error: cannot find witness
    case true =>
      var z {:trigger F(z)} :| Q(z + 1); // error: cannot find witness
  }

  method ExplicitNoTrigger() {
    // The following explicitly say to go trigger-less (no warning or info is reported)
    if
    case true =>
      assert exists w {:trigger} :: Q(w + 1); // error: assertion failure
    case true =>
      assert var y {:trigger} :| Q(y + 1); F(y) == F(y); // error: cannot find witness
    case true =>
      var z {:trigger} :| Q(z + 1); // error: cannot find witness
  }

  method NoNeedForExists() {
    // The following would not have triggers, but with the "assume", there is no need for a trigger, so nothing is reported
    if
    case true =>
      var z0 :| assume Q(z0);
    case true =>
      var z1 :| assume Q(z1 + 1);
  }
}

module GuardedIf {
  predicate Q(x: int)
  function F(x: int): int

  ghost method Test(x: int) returns (b: bool)
    ensures b ==> !Q(x)
  {
    b := true;
    if w :| Q(w) { // trigger: Q(w)
      b := false;
    }
  }

  ghost method NothingToTriggerOn() {
    if w :| Q(w + 1) { // warning: no trigger
    }
  }

  ghost method NoWarn() {
    if w {:nowarn} :| Q(w + 1) { // info: no trigger
    }
  }

  ghost method ManualTriggerThatWorks(x: int) returns (b: bool)
    ensures b && F(x) == 20 ==> !Q(x)
  {
    b := true;
    if w {:trigger F(w)} :| Q(w) {
      b := false;
    }
  }

  ghost method ManualTriggerThatDoesNotWork(x: int) returns (b: bool)
    ensures b && F(x) == 20 ==> !Q(x)
  { // error: cannot prove postcondition
    b := true;
    if w {:trigger F(w)} :| Q(w + 1) {
      b := false;
    }
  }

  ghost method ManualExplicitNoTrigger(x: int) returns (b: bool)
    ensures b && F(x) == 20 ==> !Q(x)
  { // error: cannot prove postcondition
    b := true;
    if w {:trigger} :| Q(w + 1) {
      b := false;
    }
  }
}

module GuardedIfCase {
  predicate Q(x: int)
  function F(x: int): int

  ghost method Test(x: int) returns (b: bool)
    ensures b ==> !Q(x)
  {
    if
    case !Q(x) =>
      b := true;
    case w :| Q(w) => // trigger: Q(w)
      b := false;
  }

  ghost method NothingToTriggerOn(x: int) {
    if // error: cannot prove cases are exhaustive
    case !Q(x) =>
    case w :| Q(w + 1) => // warning: no trigger
  }

  ghost method NoWarn(x: int) {
    if // error: cannot prove cases are exhaustive
    case !Q(x) =>
    case w {:nowarn} :| Q(w + 1) => // info: no trigger
  }

  ghost method ManualTriggerThatWorks(x: int) returns (b: bool)
    requires F(x) == 20
    ensures b ==> !Q(x)
  {
    if
    case !Q(x) =>
      b := *;
    case w {:trigger F(w)} :| Q(w) =>
      b := false;
  }

  ghost method ManualTriggerThatDoesNotWork(x: int) returns (b: bool)
    requires F(x) == 20
    ensures b ==> !Q(x)
  {
    if // error: cannot prove cases are exhaustive
    case !Q(x) =>
      b := *;
    case w {:trigger F(w)} :| Q(w + 1) =>
      b := false;
  }

  ghost method ManualExplicitNoTrigger(x: int) returns (b: bool)
    requires F(x) == 20
    ensures b ==> !Q(x)
  {
    if // error: cannot prove cases are exhaustive
    case !Q(x) =>
      b := *;
    case w {:trigger} :| Q(w + 1) =>
      b := false;
  }
}

module Hints {
  predicate P(y: int)

  method M0() returns (x: int) {
    x :| 0 <= x; // all is good, because a trigger is found (through the witness guessed by Dafny)
  }

  method M1() returns (x: int) {
    x :| 0 <= x && false; // error: cannot prove existence of x and there's no trigger, so error message contains hint
  }

  method M2() returns (x: int) {
    x :| P(x); // error: cannot prove existence of x, but there is a trigger, so the error message contains no hint; trigger: P(x)
  }

  method M3(y: int) returns (x: int)
    requires P(y)
  {
    x :| P(x); // trigger: P(x)
  }

  ghost function F0(): int {
    var x :| 0 <= x; // all is good, because a trigger is found (through the witness guessed by Dafny)
    x
  }

  ghost function F1(): int {
    var x :| 0 <= x && false; // error: cannot prove existence of x and there's no trigger, so error message contains hint
    x
  }

  ghost function F2(): int {
    var x :| P(x); // error: cannot prove existence of x, but there is a trigger, so the error message contains no hint; trigger: P(x)
    x
  }

  ghost function F3(y: int): int
    requires P(y)
  {
    var x :| P(x); // trigger: P(x)
    x
  }
}
