// RUN: %dafny /compile:3 /env:0 /dprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var m := new M0.MyClass.Init(20);
  print m.a, ", ", m.b, ", ", m.c, "\n";
  var r0 := new Regression.A.Make0();
  var r1 := new Regression.A.Make1();
  assert r0.b != r1.b;
  print r0.b, ", ", r1.b, "\n";
}

module M0 {
  class MyClass {
    var a: nat
    const b := 17
    var c: real
  
    constructor Init(x: nat)
    {
      this.a := x;
      c := 3.14;
      new;
      a := a + b;
      assert c == 3.14;
      assert this.a == 17 + x;
    }

    constructor (z: real)
      ensures c <= 2.0 * z
    {
      a, c := 50, 2.0 * z;
      new;
    }

    constructor Make()
      ensures 10 <= a
    {
      new;
      a := a + b;
    }

    constructor Create()
      ensures 30 <= a
    {
      new;
      a := a + 2*b;
    }
  }
}

module M1 refines M0 {
  class MyClass {
    const d := 'D';
    var e: char;

    constructor Init...
    {
      e := 'e';
      new;
      e := 'x';
      ...;
      assert e == 'x';
    }

    constructor ...
    {
      e := 'y';
      new;
    }

    constructor Make...
    {
      new;
      e := 'z';
    }

    constructor Create...
    {
      e := 'w';
    }
  }
}

module TypeOfThis {
  class LinkedList<T(0)> {
    ghost var Repr: set<LinkedList<T>>
    ghost var Rapr: set<LinkedList?<T>>
    ghost var S: set<object>
    ghost var T: set<object?>

    constructor Init()
    {
      Repr := {this};  // regression test: this should pass, but once upon a time didn't
    }

    constructor Init'()
    {
      Rapr := {this};
    }

    constructor Create()
    {
      S := {this};  // regression test: this should pass, but once upon a time didn't
    }

    constructor Create'()
    {
      T := {this};
    }

    constructor Two()
    {
      new;
      var ll: LinkedList? := this;
      var o: object? := this;
      if
      case true =>  T := {o};
      case true =>  S := {o};
      case true =>  Repr := {ll};
      case true =>  Rapr := {ll};
      case true =>  S := {ll};
      case true =>  T := {ll};
    }
  
    method Mutate()
      modifies this
    {
      Repr := {this};
      Rapr := {this};
      S := {this};
      T := {this};
    }
  }
}

module Regression {
  class A {
    var b: bool
    var y: int

    constructor Make0()
      ensures b == false  // regression test: this didn't used to be provable :O
    {
      b := false;
    }
    constructor Make1()
      ensures b == true
    {
      b := true;
    }
    constructor Make2()
    {
      b := false;
      new;  // this sets "alloc" to "true", and the verifier previously was not
            // able to distinguish the internal field "alloc" from other boolean
            // fields
      assert !b;  // regression test: this didn't used to be provable :O
    }
    constructor Make3()
      ensures b == false && y == 65
    {
      b := false;
      y := 65;
      new;
      assert !b;  // regression test: this didn't used to be provable :O
      assert y == 65;
    }
    constructor Make4(bb: bool, yy: int)
      ensures b == bb && y == yy
    {
      b, y := bb, yy;
    }
  }
}

