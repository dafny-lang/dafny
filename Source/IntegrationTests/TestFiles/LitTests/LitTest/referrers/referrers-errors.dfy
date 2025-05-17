// RUN: %exits-with 4 %verify --referrers --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Test {
  var x: Test?
  var y: Test?
  const z: Test? := null;
}

method MethodMightNotRestoreReferrers() {
  var t = new Test();
  assert referrers(t) == {locals`t};
  CallSubMethod(t);
  assert referrers(t) == {locals`t}; // Error: Cannot prove this
}

// No referrers clause means we don't know what happens to any object.
method CallSubMethod(t: Test)
{
}

method EnsuresReferrersUnchanged(t2: Test)
  ensures old(referrers(t2)) == referrers(t2)
{
  var t_local := t2;
  assert referrers(t_local) == old(referrers(t_local)) + {locals`t_local}; // Error, t_local was not assigned
}