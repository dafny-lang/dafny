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

class ChainingObjectError {
  var x: ChainingObjectError?
  var y: ChainingObjectError?
  ghost var nontracking: ChainingObjectError?
  ghost var {:tracking} tracking: ChainingObjectError?
  const tail: ChainingObjectError?
  constructor(chained_test: ChainingObjectError?) ensures x == y == nontracking == tracking == null && tail == chained_test
    ensures chained_test != null ==> referrers(chained_test) == old(referrers(chained_test)) + {this`tail}
    ensures forall o: object | o != chained_test :: referrers(o) == old(referrers(o)) // Replace by referrers clauses when they arrive
  {
    x := null;
    y := null;
    tracking := null;
    nontracking := null;
    tail := chained_test;
  }
}


method ObjectFields() {
  var t := new ChainingObject(null);
  var u := new ChainingObject(t);
  // Assignment of array
  var a := new ChainingObject[3](i => if i == 0 then t else u);
  assert referrers(t) == {locals`t, u`tail, a`[0]};
  assert referrers(u) == {locals`t, u`x, a`[1], a`[2]};

  assert false; // There should be no contradiction.
}