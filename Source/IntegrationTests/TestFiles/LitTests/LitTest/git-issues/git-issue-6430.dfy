// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Test for issue #6430: reads * on a function should not allow proving false
module M0 {
  class C {
    var o: object?
  }

  class D {
    var obj1: object?
    var obj2: object?

    function GetObj1(): object?
      reads this
    {
      obj1
    }

    function GetObj2(): object?
      reads this
    {
      obj2
    }

    function GetObj(c: C): object?
      reads *
    {
      if c.o == null then GetObj1() else GetObj2()
    }

    method Test()
      requires obj1 != obj2
    {
      assert GetObj1() != GetObj2();
      var c := new C;
      c.o := null;
      var o1 := GetObj(c);
      assert o1 == GetObj1();
      c.o := new C;
      var o2 := GetObj(c);
      assert o2 == GetObj2();
      assert o1 == o2; // error: should not be provable
      assert GetObj1() == GetObj2(); // (this line follows from the previous)
      assert false; // (and this line follows from the previous)
    }
  }
}

// Here is another test, which had been a simpler repro for the issue
module M1 {
  class C {
    var o: bool
  }

  class D {
    const aa: int
    const bb: int

    constructor (a: int, b: int)
      ensures aa == a && bb == b
    {
      aa, bb := a, b;
    }

    function Get(c: C): int
      reads *
    {
      if c.o then this.aa else this.bb
    }

    method Test()
      requires aa != bb
      ensures false
    {
      var c := new C;

      c.o := true;
      var o1 := Get(c);
      assert o1 == this.aa;

      c.o := false;
      var o2 := Get(c);
      assert o2 == this.bb;

      assert o1 == o2; // error (but before the fix, this assertion had passed)
    }
  }

  // Here's a Main method that (before the fix) showed that one can really get to the soundness bug
  method Main() {
    var d := new D(20, 22);
    d.Test();
    print 20 / 0;
  }
}

// Here is simpler test yet. Before the fix, the assertion in this test had also been bogusly provable.
module M2 {
  class C {
    var value: int
  }

  function Select(c: C, aa: int, bb: int): int
    reads *
  {
    if c.value == 101 then aa else bb
  }

  method Test(aa: int, bb: int)
    requires aa != bb
    ensures false
  {
    var c := new C;

    c.value := 101;
    var xx := Select(c, aa, bb);
    assert xx == aa;

    c.value := 102;
    var yy := Select(c, aa, bb);
    assert yy == bb;

    assert xx == yy; // error (but before the fix, this assertion had passed)
  }
}
