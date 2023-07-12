// RUN: %exits-with 4 %baredafny verify --concurrent %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class A {
  var x: nat
}

method TowardsZero(a: A, b: A)
  modifies a, b
{
  
  if * {
    assert readLocked(a);   // Fails
    assert modifyLocked(a); // Fails
  }
  if * {
    assert !modifyLocked(a); // Fails
    assert !readLocked(a);   // Fails
  }
  if * {
    var b := a.x;
    var c := a.x;
    assert b == c;            // Fails
    assert a.x == a.x;        // OK because ghost expression, same heap!

    a.x := 5;               // Fails but assumes modifyLocked(a)
    var b1 := a.x;
    var c1 := a.x;
    assert b1 == c1;        // Ok because modifyLocked(a) assumed
    a.x := 6;               // OK
  }
  lockRead(a) {
    if * {
      assert readLocked(a);   // OK
      assert modifyLocked(a); // Fails
    }
    if * {
      assert !modifyLocked(a); // Fails
    }
    var b := a.x;
    var c := a.x;
    assert b == c;            // Ok

    a.x := 5;               // Fails
    a.x := 6;               // OK
  }
  if * {
    assert readLocked(a);   // Fails
    assert modifyLocked(a); // Fails
  }
  if * {
    assert !modifyLocked(a); // Fails
    assert !readLocked(a);   // Fails
  }
  lockModify(a) {
    if * {
      assert readLocked(a);   // OK
      assert modifyLocked(a); // OK
    }
    var b := a.x;
    var c := a.x;
    assert b == c;            // Ok

    a.x := 5;               // OK
    a.x := 6;               // OK
  }
  if * {
    assert readLocked(a);   // Fails
    assert modifyLocked(a); // Fails
  }
  if * {
    assert !modifyLocked(a); // Fails
    assert !readLocked(a);   // Fails
  }
}