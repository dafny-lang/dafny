// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype NativeNotZero = x: int | 1 <= x < 255 witness 1

// k0 is initialized using var_init!<T>
// A tracker starts before the second if to determine if k needs to be cleaned up
method TestResourceCleanup<T(0)>(return_first: bool, update_value: bool, thn: T)
  requires return_first ==> !update_value
{
  var k0: T;
  if return_first {
    return; // No assignment, need to forget unconditionally about k0;
  }
  if update_value {
    k0 := thn;
  }
  // Need to forget conditionally about k0 using the tracker
}


// j1 and k1 are initialized using var_init!<T>
// Both j1 and k1 use assign_nodrop! the first time and regular assignment the second time.
// No cleanup is necessary
method TakeAssignNoDrop<T>(b: bool, thn: T, els: T) returns (j1: T, k1: T)
{
  if b {
    var x: T;
    k1 := thn;
    // Here x must be forgotten
  } else {
    var y: T;
    k1 := els;
    // Here y must be forgotten
  }
  j1 := k1;
  // Regular assignments
  k1 := j1;
  j1 := k1;
  // No cleanup necessary
}

// k02 are initialized using var_init!<T>
// A tracker starts before the second if to determine if k needs to be cleaned up
method TestResourceCleanupLoop<T>(return_first: bool, update_value: bool, thn: T)
{
  var k2: T;
  var tmp := update_value;
  while return_first {
    return; // No assignment, need to forget unconditionally about k2;
  }
  while tmp decreases tmp {
    k2 := thn;
    tmp := false;
  }
  // Need to forget conditionally about k0 using the tracker
}


// k02 are initialized using var_init!<T>
// A tracker starts before the second if to determine if k needs to be cleaned up
method TestResourceCleanupLoopComplex<T>(return_first: bool, update_value: bool, thn: T)
{
  var k2: T;
  var tmp := update_value;
  var i := 1;
  // The assignment tracker should be emitted before the while statement.
  while return_first && i >= 0 decreases i {
    if i == 0 {
      return; // No assignment, need to forget unconditionally about k0;
    } else {
      k2 := thn;
    }
    i := i -1;
  }
  i := 2;
  while i >= 0 decreases i {
    var local_var: T;
    if i == 1 {
      local_var := thn;
    }
    if(!update_value) { // Here both k2 and local_var must be forgotten
      return;
    }
    k2 := thn;
    i := i - 1;
     // local_var should be forgotten if it was never assigned here.
  }
  // Need to forget conditionally about k0 using the tracker
}




// k3 is initialized using 0. We don't care because we won't read this value before it's written to.
// A tracker starts before the second if to determine if k needs to be cleaned up
method TestResourceCleanupNative(return_first: bool, update_value: bool, thn: NativeNotZero)
{
  var k3: NativeNotZero;
  if return_first {
    return; //No need to forget numbers
  }
  if update_value {
    k3 := thn;
  }
  // No need to forget conditionally
}


// No tracking, no initialization needed.
method TakeAssignNoDropNative(b: bool, thn: NativeNotZero, els: NativeNotZero) returns (j4: NativeNotZero)
{
  var k4: NativeNotZero;
  if b {
    k4 := thn;
  } else {
    k4 := els;
  }
  j4 := k4;
  // Regular assignments
  k4 := j4;
  j4 := k4;
  // No cleanup necessary
}

// k0 are initialized using var_init!<T>
// A tracker starts before the second if to determine if k needs to be cleaned up
method TestResourceCleanupLoopNative(return_first: bool, update_value: bool, thn: NativeNotZero)
{
  var k5: NativeNotZero;
  var tmp := update_value;
  while return_first {
    return; // No assignment, need to forget unconditionally about k0;
  }
  while tmp decreases tmp {
    k5 := thn;
    tmp := false;
  }
  // Need to forget conditionally about k0 using the tracker
}

// j1 is a DafnyInt which uses the default value of a .
method AssignNoDropTwice(x: bool) returns (j6: int)
{
  if x {
    j6 := 3; // Assigned with assign_nodrop!
    return;  // No need to clean up
  }
  j6 := 1; // Assigned with assign_nodrop!
  // No need to clean up
}

method AssignNoDropTwiceNative(x: bool) returns (j7: NativeNotZero)
{
  if x {
    j7 := 3; // Assigned with regular assignment
    return;
  }
  j7 := 1;
}

method InitiateInt(x: bool, y: bool) returns (j8: int)
  requires x == y
{
  var k8: int;
  // Assignment tracking starts here for k
  if x {
    k8 := 3;
  }
  // Assignment tracking starts here for j
  if y {
    j8 := k8;
    return;
  } else {
    j8 := 3;
  }
  // J determined to be deterministically assigned here.
  // Normal assignment
  j8 := 1;
}

method Main() {
  TestResourceCleanup(true, false, 1);
  TestResourceCleanup(false, true, 1);
  TestResourceCleanup(false, false, 1);
  
  TestResourceCleanupLoop(true, false, 1);
  TestResourceCleanupLoop(false, true, 1);
  TestResourceCleanupLoop(false, false, 1);

  TestResourceCleanupLoopComplex(true, false, 1);
  TestResourceCleanupLoopComplex(false, true, 1);
  TestResourceCleanupLoopComplex(false, false, 1);
  
  TestResourceCleanupNative(true, false, 1);
  TestResourceCleanupNative(false, true, 1);
  TestResourceCleanupNative(false, false, 1);
  
  TestResourceCleanupLoopNative(true, false, 1);
  TestResourceCleanupLoopNative(false, true, 1);
  TestResourceCleanupLoopNative(false, false, 1);

  var x: int, x2: int := TakeAssignNoDrop(true, 2, 3);
  expect x == 2 == x2;
  x, x2 := TakeAssignNoDrop(false, 2, 3);
  expect x == 3;

  var y: NativeNotZero := TakeAssignNoDropNative(true, 2, 3);
  expect y == 2;
  y := TakeAssignNoDropNative(false, 2, 3);
  expect y == 3;

  x := AssignNoDropTwice(true);
  expect x == 3;
  x := AssignNoDropTwice(false);
  expect x == 1;
  y := AssignNoDropTwiceNative(true);
  expect y == 3;
  y := AssignNoDropTwiceNative(false);
  expect y == 1;

  x := InitiateInt(true, true);
  expect x == 3;
  x := InitiateInt(false, false);
  expect x == 1;
  print "Everything ok";
}