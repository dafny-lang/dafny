// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Twostate {
  var z: int

  twostate predicate Increase()
    reads this
  {
    old(z) <= z
  }

  twostate predicate NoChange()
    reads this
  {
    unchanged(this)
  }

  static twostate predicate IsFresh(new c: Twostate)
  {
    fresh(c)
  }

  twostate predicate All(new c: Twostate)
    reads this
  {
    Increase() && NoChange() && IsFresh(c)
  }

  method Test0()
    modifies this
  {
    z := z + 1;
    label L:
    z := z - 1;
    // the following line was once translated incorrectly without the @L
    assert Increase@L(); // error: does not hold
    assert false;
  }

  method Test1()
    modifies this
  {
    z := z + 1;
    label L:
    z := z - 1;
    // the following line was once translated incorrectly without the @L
    assert NoChange@L(); // error: does not hold
  }

  method Test2()
    modifies this
  {
    z := z + 1;
    label L:
    z := z - 1;
    // the following line was once translated incorrectly without the @L
    assert IsFresh@L(this); // error: does not hold
  }

  method Test3()
  {
    var c := new Twostate;
    label L:
    if * {
      // the following line was once translated incorrectly without the @L
      assert IsFresh@L(c); // error: does not hold
    } else {
      assert IsFresh(c);
    }
  }

  method Test4()
    modifies this
  {
    var c := new Twostate;
    z := z + 1;
    label L:
    z := z - 1;
    // the following line was once translated incorrectly without the @L
    assert All@L(c); // error: does not hold
  }

  method Test5(k: nat)
    modifies this
  {
    z := z + k;
    label L:
    var c := new Twostate;

    assert Increase@L();
    assert NoChange@L();
    assert IsFresh@L(c);

    assert Increase();
    if k == 0 {
      assert NoChange();
    }
    assert IsFresh(c);
  }

  method Test6()
    modifies this
  {
    z := z + 1;
    var c := new Twostate;
    label L:
    z := z - 1;

    assert Increase();
    assert NoChange();
    assert IsFresh(c);
  }

  method Test7()
    modifies this
  {
    z := z + 1;
    label L:
    var c := new Twostate;
    assert All@L(c);
  }

  method FreeHeapAtVariables()
    modifies this
  {
    z := z + 1;
    label L:
    z := z - 1;
    ghost var x;
    // regression: the following line once led to malformed Boogie
    x := var u :| u == Increase@L(); !u;
    assert x;
  }
}
