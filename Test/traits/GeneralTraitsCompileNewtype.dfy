// RUN: %dafny /compile:0 /generalTraits:1 /typeSystemRefresh:1 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /generalTraits:1 /typeSystemRefresh:1 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /generalTraits:1 /typeSystemRefresh:1 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /generalTraits:1 /typeSystemRefresh:1 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /generalTraits:1 /typeSystemRefresh:1 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  TypeTestsAndConversions.Test();
  Methods.Test();
  Functions.Test();
  Consts.Test();
}

module TypeTestsAndConversions {
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
  // TODO (for the verifier):  assert x == x' == x'' == x == mi == p == g == w == x;

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
    MakeCallsAsMyInt(mi); // hello MyInt: 10 11 12 13 14
    var p: ParentTrait := mi;
    MakeCallsAsParent(p); // hello Parent: 10 11 12 13
    var g: GrandParentTrait := mi;
    g := p;
    MakeCallsAsGrandParent(g); // hello GrandParent: 10 11 12
  }

  method MakeCallsAsMyInt(mi: MyInt) {
    print "hello MyInt: ";
    print mi.A(), " ";
    print mi.B(), " ";
    print mi.C(), " ";
    print mi.D(), " ";
    print mi.E(), "\n";
  }

  method MakeCallsAsParent(p: ParentTrait) {
    print "hello Parent: ";
    print p.A(), " ";
    print p.B(), " ";
    print p.C(), " ";
    print p.D(), "\n";
  }

  method MakeCallsAsGrandParent(g: GrandParentTrait) {
    print "hello GrandParent: ";
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
    ReadConstsAsMyInt(mi); // hello MyInt: 10 11 12
    var p: ParentTrait := mi;
    ReadConstsAsParent(p); // hello Parent: 10 11
    var g: GrandParentTrait := mi;
    g := p;
    ReadConstsAsGrandParent(g); // hello GrandParent: 10
  }

  method ReadConstsAsMyInt(mi: MyInt) {
    print "hello MyInt: ";
    print mi.A, " ";
    print mi.B, " ";
    print mi.C, "\n";
  }

  method ReadConstsAsParent(p: ParentTrait) {
    print "hello Parent: ";
    print p.A, " ";
    print p.B, "\n";
  }

  method ReadConstsAsGrandParent(g: GrandParentTrait) {
    print "hello GrandParent: ";
    print g.A, "\n";
  }
}
