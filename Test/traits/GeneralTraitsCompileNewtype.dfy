// RUN: %dafny /compile:0 /generalTraits:1 /typeSystemRefresh:1 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /generalTraits:1 /typeSystemRefresh:1 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /generalTraits:1 /typeSystemRefresh:1 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /generalTraits:1 /typeSystemRefresh:1 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /generalTraits:1 /typeSystemRefresh:1 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /generalTraits:1 /typeSystemRefresh:1 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  Basics.Test();
  TypeTestsAndConversions.Test();
  Methods.Test();
  Functions.Test();
  Consts.Test();
//  TailRecursion.Test();
}

module Basics {
  trait Trait {
    method MethodDefinedInTrait() {
      print "A";
    }
    method VirtualMethodInTrait()
  }

  newtype MyInt extends Trait = x | 0 <= x < 100
  {
    method VirtualMethodInTrait() {
      print "B";
    }
    method MethodDefinedInNewtype() {
      print "C";
    }
  }

  datatype Datatype extends Trait = Water(int) | Fire(bool)
  {
    method VirtualMethodInTrait() {
      print "D";
    }
    method MethodDefinedInDatatype() {
      print "E";
    }
  }

  class Class extends Trait {
    method VirtualMethodInTrait() {
      print "F";
    }
    method MethodDefinedInClass() {
      print "G";
    }
  }

  method Test() {
    var mi: MyInt := 27;
    var tt: Trait := mi;
    var uu: MyInt := tt as MyInt;
    print mi, " ", tt, " ", uu, "\n"; // 27 27 27

    mi.MethodDefinedInTrait();
    mi.VirtualMethodInTrait();
    mi.MethodDefinedInNewtype();
    print " ";
    tt.MethodDefinedInTrait();
    tt.VirtualMethodInTrait();
    print "\n"; // ABC AB

    var d: Datatype := Water(150);
    tt := d;

    d.MethodDefinedInTrait();
    d.VirtualMethodInTrait();
    d.MethodDefinedInDatatype();
    print " ";
    tt.MethodDefinedInTrait();
    tt.VirtualMethodInTrait();
    print "\n"; // ADE DE

    var c: Class := new Class;
    tt := c;

    c.MethodDefinedInTrait();
    c.VirtualMethodInTrait();
    c.MethodDefinedInClass();
    print " ";
    tt.MethodDefinedInTrait();
    tt.VirtualMethodInTrait();
    print "\n"; // AFG FG
  }
}

module TypeTestsAndConversions {
  trait GrandParentTrait { }

  trait ParentTrait extends GrandParentTrait { }

  newtype MyInt extends ParentTrait = x | 0 <= x < 100

  method Test() {
    var mi: MyInt := 15;
    var p: ParentTrait := mi;
    var g: GrandParentTrait := mi;

    assert mi is MyInt && p is MyInt && g is MyInt;
    assert mi is ParentTrait && p is ParentTrait && g is ParentTrait;
    assert mi is GrandParentTrait && p is GrandParentTrait && g is GrandParentTrait;
    print mi is MyInt, " ", p is MyInt, " ", g is MyInt, "\n"; // true true true
    print mi is ParentTrait, " ", p is ParentTrait, " ", g is ParentTrait, "\n"; // true true true
    print mi is GrandParentTrait, " ", p is GrandParentTrait, " ", g is GrandParentTrait, "\n"; // true true true

    var w: ParentTrait := g as ParentTrait;
    var x: MyInt := p as MyInt;
    var x': MyInt := g as MyInt;
    var x'': MyInt := mi as MyInt;
    assert x == x' == x'' == x == mi == p == g == w == x;

    print mi, " ", p, " ", g, " -- ", x, " ", x', " ", x'', "\n"; // 15 15 15 -- 15 15 15
  }
}

module Methods {
  trait GrandParentTrait {
    method A() {
      print " A";
    }
    method B()
    method C()
  }

  trait ParentTrait extends GrandParentTrait {
    method B() {
      print " B";
    }
    method D()
  }

  newtype MyInt extends ParentTrait = x | 0 <= x < 100
  {
    method C() {
      print " C";
    }
    method D() {
      print " D";
    }
    method E() {
      print " E";
    }
  }

  method Test() {
    var mi: MyInt := 15;
    MakeCallsAsMyInt(mi); // hello MyInt: A B C D E
    var p: ParentTrait := mi;
    MakeCallsAsParent(p); // hello Parent: A B C D
    var g: GrandParentTrait := mi;
    g := p;
    MakeCallsAsGrandParent(g); // hello GrandParent: A B C
  }

  method MakeCallsAsMyInt(mi: MyInt) {
    print "hello MyInt:";
    mi.A();
    mi.B();
    mi.C();
    mi.D();
    mi.E();
    print "\n";
  }

  method MakeCallsAsParent(p: ParentTrait) {
    print "hello Parent:";
    p.A();
    p.B();
    p.C();
    p.D();
    print "\n";
  }

  method MakeCallsAsGrandParent(g: GrandParentTrait) {
    print "hello GrandParent:";
    g.A();
    g.B();
    g.C();
    print "\n";
  }
}

module Functions {
  trait GrandParentTrait {
    function A(): int {
      0xA
    }
    function B(): int
    function C(): int
  }

  trait ParentTrait extends GrandParentTrait {
    function B(): int {
      0xB
    }
    function D(): int
  }

  newtype MyInt extends ParentTrait = x | 0 <= x < 100
  {
    function C(): int {
      0xC
    }
    function D(): int {
      0xD
    }
    function E(): int {
      0xE
    }
  }

  method Test() {
    var mi: MyInt := 9;
    MakeCallsAsMyInt(mi); // hi MyInt: 10 11 12 13 14
    var p: ParentTrait := mi;
    MakeCallsAsParent(p); // hi Parent: 10 11 12 13
    var g: GrandParentTrait := mi;
    g := p;
    MakeCallsAsGrandParent(g); // hi GrandParent: 10 11 12
  }

  method MakeCallsAsMyInt(mi: MyInt) {
    print "hi MyInt: ";
    print mi.A(), " ";
    print mi.B(), " ";
    print mi.C(), " ";
    print mi.D(), " ";
    print mi.E(), "\n";
  }

  method MakeCallsAsParent(p: ParentTrait) {
    print "hi Parent: ";
    print p.A(), " ";
    print p.B(), " ";
    print p.C(), " ";
    print p.D(), "\n";
  }

  method MakeCallsAsGrandParent(g: GrandParentTrait) {
    print "hi GrandParent: ";
    print g.A(), " ";
    print g.B(), " ";
    print g.C(), "\n";
  }
}

module Consts {
  trait GrandParentTrait {
    const A: int := 0xA
  }

  trait ParentTrait extends GrandParentTrait {
    const B: int := 0xB
  }

  newtype MyInt extends ParentTrait = x | 0 <= x < 100
  {
    const C: int := 0xC
  }

  method Test() {
    var mi: MyInt := 9;
    ReadConstsAsMyInt(mi); // tjena MyInt: 10 11 12
    var p: ParentTrait := mi;
    ReadConstsAsParent(p); // tjena Parent: 10 11
    var g: GrandParentTrait := mi;
    g := p;
    ReadConstsAsGrandParent(g); // tjena GrandParent: 10
  }

  method ReadConstsAsMyInt(mi: MyInt) {
    print "tjena MyInt: ";
    print mi.A, " ";
    print mi.B, " ";
    print mi.C, "\n";
  }

  method ReadConstsAsParent(p: ParentTrait) {
    print "tjena Parent: ";
    print p.A, " ";
    print p.B, "\n";
  }

  method ReadConstsAsGrandParent(g: GrandParentTrait) {
    print "tjena GrandParent: ";
    print g.A, "\n";
  }
}
/*****
module TailRecursion {
  method Test() {
    var mi: MyInt := 29;
    var dt: IntList := Cons(8, Nil);
    var c: C := new C;

    var s: seq<Trait> := [mi, dt, c];
    for i := 0 to |s| {
      var p: Trait := s[i];
      p.Print();
      p.A(31);
      p.B(31);
      print p.F(25), " ", p.G(25), "\n";
    }

    // test compilation of additional expressions, to make sure the necessary coercions are used
    s := s[2 := mi];
    print s, "\n";

/*
    var m := map[0 := mi, 1 := dt];//[2 := c][3 := mi][2 := mi];
    m := m[2 := c];
    m := [3 := mi];
    m := [2 := mi];
    print m, "\n";
*/
/*
    var p: Trait := mi;
    var pair: (Trait, Trait) := (mi, p);
    pair := (p, mi);
    print pair, "\n";
 */
//    var arrFromDisplay := new Trait[] [mi, dt, c];
//    var arrFromLambda := new Trait[3](i requires 0 <= i < 3 => s[i]);
//    var arr := new Trait[3]; // error: cannot initialize Trait
  }

  trait Trait {
    predicate GoodToPrint()
    method Print() {
      if GoodToPrint() {
        print this, "\n";
      } else {
        print "Not so good to print\n";
      }
    }
    method {:tailrecursion} A(n: nat) {
      if n != 0 {
        A(n - 1);
      }
    }
    method B(n: nat)
      decreases n
    function {:tailrecursion} F(n: nat): nat {
      if n == 0 then 0 else 1 + F(n - 1)
    }
    function G(n: nat): nat
      decreases n
  }

  newtype MyInt extends Trait = x | 0 <= x < 100
  {
    predicate GoodToPrint() {
      true
    }
    method {:tailrecursion} B(n: nat)
      decreases n
    {
      if n == 7 {
        print "MyInt.B(7) reached\n";
      }
      if n != 0 {
        B(n - 1);
      }
    }
    function G(n: nat): nat
      decreases n
    {
      if n == 0 then 0 else 100 + G(n - 1)
    }
  }

  datatype IntList extends Trait = Nil | Cons(int, IntList) {
    predicate GoodToPrint() {
      true
    }
    method {:tailrecursion} B(n: nat)
      decreases n
    {
      if n == 7 {
        print "IntList.B(7) reached\n";
      }
      if n != 0 {
        B(n - 1);
      }
    }
    function G(n: nat): nat
      decreases n
    {
      if n == 0 then 1 else 100 + G(n - 1)
    }
  }

  class C extends Trait {
    predicate GoodToPrint() {
      false
    }
    method {:tailrecursion} B(n: nat)
      decreases n
    {
      if n == 7 {
        print "C.B(7) reached\n";
      }
      if n != 0 {
        B(n - 1);
      }
    }
    function G(n: nat): nat
      decreases n
    {
      if n == 0 then 2 else 100 + G(n - 1)
    }
  }
}
*****/
