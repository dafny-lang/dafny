class C {
  var data: int;
}

method M0(IS: set<int>)
{
  parallel (i | 0 <= i < 20) {
    i := i + 1;  // error: not allowed to assign to bound variable
  }

  var k := 0;
  parallel (i | 0 <= i < 20) {
    k := k + i;  // error: not allowed to assign to local k, since k is not declared inside parallel block
  }

  parallel (i | 0 <= i < 20)
    ensures true;
  {
    var x := i;
    x := x + 1;
  }

  ghost var y;
  var z;
  parallel (i | 0 <= i)
    ensures true;
  {
    var x := i;
    x := x + 1;
    y := 18;  // (this statement is not allowed, since y is declared outside the parallel, but that check happens only if the first resolution pass of the parallel statement passes, which it doesn't in this case because of the next line)
    z := 20;  // error: assigning to a non-ghost variable inside a ghost parallel block
  }

  parallel (i | 0 <= i)
    ensures true;
  {
    ghost var x := i;
    x := x + 1;  // cool
  }

  var ia := new int[20];
  parallel (i | 0 <= i < 20) {
    ia[i] := choose IS;  // error: set choose not allowed
  }

  var ca := new C[20];
  parallel (i | 0 <= i < 20) {
    ca[i] := new C;  // error: new allocation not allowed
  }
  parallel (i | 0 <= i < 20)
    ensures true;
  {
    var c := new C;  // error: new allocation not allowed
  }
}

method M1() {
  parallel (i | 0 <= i < 20) {
    assert i < 100;
    if (i == 17) { break; }  // error: nothing to break out of
  }

  parallel (i | 0 <= i < 20) ensures true; {
    if (i == 8) { return; }  // error: return not allowed inside parallel block
  }

  var m := 0;
  label OutsideLoop:
  while (m < 20) {
    parallel (i | 0 <= i < 20) {
      if (i == 17) { break; }  // error: not allowed to break out of loop that sits outside parallel
      if (i == 8) { break break; }  // error: ditto (also: attempt to break too far)
      if (i == 9) { break OutsideLoop; }  // error: ditto
    }
    m := m + 1;
  }

  parallel (i | 0 <= i < 20) {
    var j := 0;
    while (j < i) {
      if (j == 6) { break; }  // fine
      if (j % 7 == 4) { break break; }  // error: attempt to break out too far
      if (j % 7 == 4) { break OutsideLoop; }  // error: attempt to break to place not in enclosing scope
      j := j + 1;
    }
  }
}

// -------------------------------------------------------------------------------------
// Some soundness considerations
// -------------------------------------------------------------------------------------

ghost static method X_M0(y: int)
  ensures exists o: object :: o != null && fresh(o);  // error: not allowed 'fresh' here
{
  var p := new object;
}

class X_C { ghost var data: int; }
ghost static method X_M1(y: int)
  ensures exists c: X_C :: c != null && c.data != old(c.data);  // error: not allowed 'old' here
{
  var c := new X_C;
  c.data := c.data + 1;
}

method X_Main() {
  if (*) {
    parallel (x) { X_M0(x); }
  } else {
    parallel (x) { X_M1(x); }
  }
  assert false;
}


// The following seems to be a legitimate use of a two-state predicate in the postcondition of the parallel statement
method X_Legit(c: X_C)
  requires c != null;
  modifies c;
{
  c.data := c.data + 1;
  parallel (x | c.data <= x)
    ensures old(c.data) < x;  // error: not allowed 'old' here
  {
  }
}

// X_M2 is like X_M0, but with an out-parameter
ghost static method X_M2(y: int) returns (r: int)
  ensures exists o: object :: o != null && fresh(o);  // 'fresh' is allowed here (because there's something coming "out" of this ghost method, namely 'r'
{
  var p := new object;
}

// The following method exhibits a case where M2 and a two-state parallel ensures would lead to an unsoundness
// with the current translation.
method X_AnotherMain(c: X_C)
  requires c != null;
  modifies c;
{
  c.data := c.data + 1;
  parallel (x: int)
    ensures exists o: object :: o != null && fresh(o);  // error: not allowed 'fresh' here
  {
    var s := X_M2(x);
  }
  assert false;
}

// -------------------------------------------------------------------------------------
