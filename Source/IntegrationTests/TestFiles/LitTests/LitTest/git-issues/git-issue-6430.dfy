// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Test for issue #6430: reads * on a function should not allow proving false

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
    assert GetObj1() == GetObj2(); // error: should not be provable
    assert false; // error: should not be provable
  }
}
