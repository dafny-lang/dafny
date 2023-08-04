// RUN: %exits-with 4 %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var g: int
  var h: int
}

// Here are examples of suppressed preconditions and assertions

method M0(x: int, y: int)
  requires 0 <= x
  requires Y: 0 <= y
{
  assert 0 <= x;
  assert 0 <= y;  // error: labeled requires is suppressed
}

iterator Iter0(x: int, y: int, z: int) yields (u: int)
  requires 0 <= x
  requires Y: 0 <= y
  requires Z: 0 <= z
{
  assert 0 <= x;
  assert 0 <= y;  // error: labeled requires is suppressed
  yield 20;
  assert A: x + y == 80;  // error: may not hold
  assert B: x + y == 80;  // error: still may not hold, and the previous assert is of no help
  assert x + y == 80;  // error: still may not hold, and the previous assert is of no help
  assert x + y == 80;  // fine
  yield 30;
  assert 0 <= z;  // error: labeled requires is suppressed
}

twostate lemma T0(c: C)
  requires old(c.g) == 10
  requires c.g == 20
  requires A: old(c.h) == 100
  requires B: c.h == 200
{
  assert old(c.g) < c.g;
  assert old(c.h) < 150;  // error: labeled requires is suppressed
  assert 150 < c.h;  // error: labeled requires is suppressed
}

method Test(c: C)
  requires c.g == 0
  modifies c
{
  var local := 1;
  c.g := local;
  label A: label AA:
  assert X: c.g == local == 1;

  local, c.g := local + 1, local + 1;
  label B: label BB:
  assert Y: c.g == local == 2;

  local, c.g := local + 1, local + 1;
  assert Z: c.g == local == 3;

  assert old(c.g) < old@A(c.g) < old@B(c.g) < c.g;
  assert old@A(local) == 3 == old@B(local);  // true, because old does not affect local variables
}

method M1(x: int, y: int, z: int)
  requires X: 0 <= x
  requires 8: 0 <= y
  requires 00_010: 0 <= z
{
  assert XX: -20 <= x by {
    reveal X;
    assert 0 <= x;
  }
  assert 88: -20 <= y by {
    reveal 8;
    assert 0 <= y;
  }
  assert 10: -20 <= z by {
    reveal 00_010;
    assert 0 <= z;
  }

  reveal XX;
  assert -20 <= x;
  reveal 88;
  assert -20 <= y;
  reveal 10;
  assert -20 <= z;
  if * {
    assert 0 <= z;  // error: this information has been suppressed
  } else {
    reveal 00_010;
    assert 0 <= z;
  }
}

method M2(x: int)
  requires 0: 0 <= x
{
  // Test that variables are correctly captured
  if * {
    var x := -8;  // shadows the parameter x
    reveal 0;  // here, we get to find out that the parameter x is non-negative
    assert 0 <= x;  // error: this assertion refers to the local variable
  } else if * {
    assert 0 <= x;  // error: nothing is known about the parameter here
  } else {
    reveal 0;
    assert 0 <= x;
  }
}

method M3(c: C, u: int)
  requires R: c.g == u
  modifies c
{
  var v := u;
  assert S: c.g == v by {
    reveal R;
  }
  c.g := c.g + 2;
  assert T: c.g == v + 2 by {
    reveal S;
  }
  if * {
    reveal R;
    assert c.g == u;  // error: the revealed R speaks about the pre-state
  } else if * {
    v := v + 3;
    reveal S;
    assert v - 1 == c.g;
  } else {
    v := v + 5;
    var vv := v;
    assert U: v - 3 == c.g by {
      reveal S;
    }
    v, c.g := 178, c.g + 100;
    if * {
      reveal U;
      assert v - 3 == c.g;  // error: wrong state
    } else {
      reveal U;
      assert old@U(c.g) == vv - 3;
      assert false;  // error: of course
    }
  }
}

iterator I1(c: C, d: C, u: int)
  requires c != d
  requires R: c.g == u
  requires R': d.g == u
  modifies c, d
  reads c
{
  var v := u;
  assert S: c.g == v by {
    reveal R;
  }
  assert S': d.g == v by {  // error: d may have been changed in the initial implicit "yield"
    reveal R';
  }
  c.g := c.g + 2;
  assert T: c.g == v + 2 by {
    reveal S;
  }
  yield;
  if * {
    reveal R;
    assert c.g == u;  // error: the revealed R speaks about the pre-state
  } else if * {
    v := v + 3;
    reveal S;
    yield;
    assert v - 1 == c.g;
  } else {
    v := v + 5;
    var vv := v;
    assert U: v - 3 == c.g by {
      reveal S;
    }
    yield;
    v, c.g := 178, c.g + 100;
    yield;
    if * {
      reveal U;
      assert v - 3 == c.g;  // error: wrong state
    } else {
      reveal U;
      assert old@U(c.g) == vv - 3;
      assert false;  // error: of course
    }
  }
}

twostate lemma T1(c: C)
  requires old(c.g) == 10
  requires c.g == 20
  requires A: old(c.h) == 100
  requires B: c.h == 200
{
  assert old(c.g) < c.g;
  if * {
    assert old(c.h) < 150;  // error: labeled requires is suppressed
    assert 150 < c.h;  // error: labeled requires is suppressed
  } else if * {
    reveal A;
    assert old(c.h) < 150;
    assert 150 < c.h;  // error: labeled requires is suppressed
  }
}

twostate lemma T2(c: C)
  requires old(c.g) == 10
  requires c.g == 20
  requires A: old(c.h) == 100
  requires B: c.h == 200
{
  assert old(c.g) < c.g;
  if * {
    reveal B;
    assert old(c.h) < 150;  // error: labeled requires is suppressed
    assert 150 < c.h;
    assert false;  // error: of course
  } else {
    reveal A;
    reveal B;
    assert old(c.h) < 150;
    assert 150 < c.h;
    assert false;  // error: of course
  }
}

lemma Calc(x: int)
  requires A: x < 10
{
  assert B: x < 150 by { reveal A; }

  calc {
    x < 200;
  ==  { reveal B; }
    x < 150;
  ==  { assert C: x < 90 by { reveal A; }
        reveal C;
      }
    x < 100;
  ==  { reveal A; }
    x < 10;
  ==
    x < 100;  // error: without a reveal in this step, it cannot be proved
  }
}

twostate lemma T3(c: C)
  requires old(c.g) == 10
  requires c.g == 20
  requires A: old(c.h) == 100
  requires B: c.h == 200
{
  reveal A, B;  // this can be a list
  assert old(c.h) < 150;
  assert 150 < c.h;
  assert false;  // error: of course
}
