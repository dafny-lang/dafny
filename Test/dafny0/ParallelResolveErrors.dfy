class C {
  var data: int;
  ghost var gdata: int;
  ghost method Init_ModifyNothing() { }
  ghost method Init_ModifyThis() modifies this;
  {
    data := 6;  // error: assignment to a non-ghost field
    gdata := 7;
  }
  ghost method Init_ModifyStuff(c: C) modifies this, c; { }
  method NonGhostMethod() { print "hello\n"; }
}

method M0(IS: set<int>)
{
  forall (i | 0 <= i < 20) {
    i := i + 1;  // error: not allowed to assign to bound variable
  }

  var k := 0;
  forall (i | 0 <= i < 20) {
    k := k + i;  // error: not allowed to assign to local k, since k is not declared inside forall block
  }

  forall (i | 0 <= i < 20)
    ensures true;
  {
    var x := i;
    x := x + 1;
  }

  ghost var y;
  var z;
  forall (i | 0 <= i)
    ensures true;
  {
    var x := i;
    x := x + 1;
    y := 18;  // (this statement is not allowed, since y is declared outside the forall, but that check happens only if the first resolution pass of the forall statement passes, which it doesn't in this case because of the next line)
    z := 20;  // error: assigning to a non-ghost variable inside a ghost forall block
  }

  forall (i | 0 <= i)
    ensures true;
  {
    ghost var x := i;
    x := x + 1;  // cool
  }

  var ia := new int[20];
  forall (i | 0 <= i < 20) {
    ia[i] := choose IS;  // error: set choose not allowed
  }

  var ca := new C[20];
  forall (i | 0 <= i < 20) {
    ca[i] := new C;  // error: new allocation not allowed
  }
  forall (i | 0 <= i < 20)
    ensures true;
  {
    var c := new C;  // allowed
    var d := new C.Init_ModifyNothing();
    var e := new C.Init_ModifyThis();
    var f := new C.Init_ModifyStuff(e);
    c.Init_ModifyStuff(d);
    c.NonGhostMethod();  // error: only allowed to call ghost methods (because of possible 'print' statements, sigh)
  }
}

method M1() {
  forall (i | 0 <= i < 20) {
    assert i < 100;
    if (i == 17) { break; }  // error: nothing to break out of
  }

  forall (i | 0 <= i < 20) ensures true; {
    if (i == 8) { return; }  // error: return not allowed inside forall block
  }

  var m := 0;
  label OutsideLoop:
  while (m < 20) {
    forall (i | 0 <= i < 20) {
      if (i == 17) { break; }  // error: not allowed to break out of loop that sits outside forall
      if (i == 8) { break break; }  // error: ditto (also: attempt to break too far)
      if (i == 9) { break OutsideLoop; }  // error: ditto
    }
    m := m + 1;
  }

  forall (i | 0 <= i < 20) {
    var j := 0;
    while (j < i) {
      if (j == 6) { break; }  // fine
      if (j % 7 == 4) { break break; }  // error: attempt to break out too far
      if (j % 7 == 4) { break OutsideLoop; }  // error: attempt to break to place not in enclosing scope
      j := j + 1;
    }
  }
}

method M2() {
  var a := new int[100];
  forall (x | 0 <= x < 100) {
    a[x] :| assume a[x] > 0;  // error: not allowed to update heap location in a forall statement with an assume
  }
}
