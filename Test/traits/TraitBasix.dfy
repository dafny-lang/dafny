// RUN: %exits-with 2 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module m1
{
  trait I1
  {
    ghost function M1(x:int,y:int) :int
    {
      x*y
    }
  }


  trait I2       //all is fine in this trait
  {
    var x: int

    function Twice(): int
      reads this
    {
      x + x
    }

    function F(z: int): int
      reads this


    method Compute(s: bool) returns (t: int, u: int)
      modifies this
    {
      if s {
        t, u := F(F(15)), Twice();
      } else {
        t := Twice();
        x := F(45);
        u := Twice();
        var p := Customizable(u);
        return t+p, u;
      }
    }

    method Customizable(w: int) returns (p: int)
      modifies this


    static method StaticM(a: int) returns (b: int)
    {
      b := a;
    }

    static method SS(a: int) returns (b:int)
    {
      b:=a*2;
    }
  }

  method I2Client(j: I2) returns (p: int)     //all is fine in this client method
    requires j != null
    modifies j
  {
    j.x := 100;
    var h := j.Twice() + j.F(j.Twice());
    var a, b := j.Compute(h < 33);
    var c, d := j.Compute(33 <= h);
    p := j.Customizable(a + b + c + d);
    p := I2.StaticM(p);
  }

  class I0Child extends I2  //errors, body-less methods/functions in the parent have not implemented here
  {
    function F(z: int): int
      reads this
    {
       z
    }
    var x: int //error, x has been declared in the parent trait
  }

  class I0Child2 extends I2
  {
    method Customizable(w: int) returns (p: int)
      modifies this
    {
       w:=w+1;
    }

    var c1: I0Child
  }
} module DoesNotExist {
  class IXChild extends IX   //error, IX trait is undefined
  {

  }
}

module MoreTests {
  trait I0
  {
    var x: int
    constructor I0(x0: int) // error: constructor is not allowed in a trait
    {
      x:=x0;
    }
  }

  trait I1
  {
    ghost function M1(x:int,y:int) :int
    {
      x*y
    }
  }

  method TestI1()
  {
    var i1 := new I1;   //error: new is not allowed in a trait
  }

  trait I2       //all is fine in this trait
  {
    var x: int

    function Twice(): int
      reads this
    {
      x + x
    }

    function F(z: int): int
      reads this


    method Compute(s: bool) returns (t: int, u: int)
      modifies this
    {
      if s {
        t, u := F(F(15)), Twice();
      } else {
        t := Twice();
        x := F(45);
        u := Twice();
        var p := Customizable(u);
        return t+p, u;
      }
    }

    method Customizable(w: int) returns (p: int)
      modifies this


    static method StaticM(a: int) returns (b: int)
    {
      b := a;
    }

    static method SS(a: int) returns (b:int)
    {
      b:=a*2;
    }
  }

  method I2Client(j: I2) returns (p: int)     //all is fine in this client method
    requires j != null
    modifies j
  {
    j.x := 100;
    var h := j.Twice() + j.F(j.Twice());
    var a, b := j.Compute(h < 33);
    var c, d := j.Compute(33 <= h);
    p := j.Customizable(a + b + c + d);
    p := I2.StaticM(p);
  }
}  // MoreTests

module TypeInference {
  trait Tr<X> { }
  class A extends Tr<int> { }
  class B extends Tr<real> { }

  method M(a: A, b: B) {
    var t;
    t := a;
    t := b;  // error: cannot assign Tr<real> to Tr<int>
  }
}  // TypeInference

module ExtendObject {
  trait A extends object { }
  trait B extends object, A { }
  trait C extends A, object { }
  class X extends object { }
  class Y extends object, A { }
  class Z extends A, object { }
}
