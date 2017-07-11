// RUN: %dafny /compile:3 /env:0 /dprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var m := new M0.MyClass.Init(20);
  print m.a, ", ", m.b, ", ", m.c, "\n";
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
