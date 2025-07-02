// RUN: %exits-with 4 %verify --referrers --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Test {
  var x: Test?
  var y: Test?
  const z: Test? := null
  constructor() {
    this.x := null;
    this.y := null;
  }
}

method MethodMightNotRestoreReferrers() {
  var t := new Test();
  assert referrers(t) == {locals`t}; // Error, we don't know since it was a constructor
  CallSubMethod(t);
  assert referrers(t) == {locals`t}; // Error: Cannot prove this
}

// No referrers clause means we don't know what happens to any object.
method CallSubMethod(t: Test)
{
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

@ResourceLimit("1e6")
@IsolateAssertions
method ObjectFields() {
  var t := new ChainingObjectError(null);
  var u := new ChainingObjectError(t);
  assert ChainingObjectError.constructor`this !in referrers(u);
  // Assignment of array
  var a := new ChainingObjectError[3](i => if i == 0 then t else u);
  assert locals`t in referrers(t);
  assert u`tail in referrers(t);
  assert a`[0] in referrers(t);
  assert referrers(t) == {locals`t, u`tail, a`[0]};
  assert referrers(u) == {locals`t, u`x, a`[1], a`[2]};

  assert false; // There should be no contradiction.
}