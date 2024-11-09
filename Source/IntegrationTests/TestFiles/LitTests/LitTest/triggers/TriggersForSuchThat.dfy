// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s" -- --show-hints

predicate Q(x: int)
function F(x: int): int

method TestSuchThat()
  requires Q(18)
{
  // In the following lines, the trigger {Q(_)} is selected automatically
  if
  case true =>
    assert exists w :: Q(w);
  case true =>
    assert var y :| Q(y); F(y) == F(y);
  case true =>
    var z :| Q(z);
}

method NothingToTriggerOn() {
  // In the following lines, there is no good trigger, so a warning is generated
  if
  case true =>
    assert exists w :: Q(w+1); // warning: no trigger; error: assertion failure
  case true =>
    assert var y :| Q(y + 1); y < 24; // warning: no trigger; error: assertion failure
  case true =>
    var z :| Q(z + 2); // warning: no trigger; error: assertion failure
}

method NoWarn() {
  // The :nowarn attribute replacing the no-trigger warning by an informational message
  if
  case true =>
    assert exists w {:nowarn} :: Q(w+1); // info: no trigger; error: assertion failure
  case true =>
    assert var y {:nowarn} :| Q(y + 1); y < 24; // info: no trigger; error: assertion failure
  case true =>
    var z {:nowarn} :| Q(z + 2); // error: info: no trigger; assertion failure
}

method ManualTriggerThatWorks()
  requires F(10) == 20
  requires Q(11)
{
  // The following lines use the manually specific trigger
  if
  case true =>
    assert exists w {:trigger F(w)} :: Q(w+1);
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
    assert exists w {:trigger F(w)} :: Q(w+1); // error: assertion failure
  case true =>
    assert var y {:trigger F(y)} :| Q(y + 1); F(y) == F(y); // error: assertion failure
  case true =>
    var z {:trigger F(z)} :| Q(z + 1); // error: assertion failure
}

method ExplicitNoTrigger() {
  // The following explicitly say to go trigger-less (no warning or info is reported)
  if
  case true =>
    assert exists w {:trigger} :: Q(w+1); // error: assertion failure
  case true =>
    assert var y {:trigger} :| Q(y + 1); y < 24; // error: assertion failure
  case true =>
    var z {:trigger} :| Q(z + 1); // error: assertion failure
}

method NoNeedForExists() {
  // The following would not have triggers, but with the "assume", there is no need for a trigger, so nothing is reported
  if
  case true =>
    var z0 :| assume Q(z0);
  case true =>
    var z1 :| assume Q(z1 + 1);
}
