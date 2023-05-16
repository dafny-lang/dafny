// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp /unicodeChar:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint32 = i:int | 0 <= i < 0x100000000

class MyClass {
  var a: uint32
  const b: uint32
  const c:uint32 := 17
  static const d: uint32
  static const e:uint32 := 18

  var ar: array<uint32>

  constructor (x: uint32)
    requires x < 100
    ensures this.a < 300
    ensures this.b < 300
    ensures fresh(this.ar)
  {
    a := 100 + x;
    b := 200 + x;
    ar := new uint32[5];
  }

  function F(): uint32 { 8 }
  static function G(): uint32 { 9 }
  method M() returns (r: uint32) { r := 69; }
  static method N() returns (r: uint32) { return 70; }

  method stuffWithAr()
    modifies this
    modifies this.ar
  {
    print "stuffWithAr\n";
    this.ar := new uint32[5];
    this.ar[0] := 5;
    print this.ar[0];
    print "\n";
  }
}

method CallEm(c: MyClass, t: MyClass, i: MyClass)
  requires c.a as int + t.a as int + i.a as int < 1000
  ensures c.ar == old(c.ar)
  modifies c, t, i
{
  // instance fields

  print c.a, " ", t.a, " ", i.a, " ";
  c.a := c.a + 3;
  t.a := t.a + 3;
  i.a := i.a + 3;
  print c.a, " ", t.a, " ", i.a, "\n";

  // (instance and static) members via instance

  var u;

  print c.b, " ";
  print c.c, " ";
  print c.d, " ";
  print c.e, " ";
  print c.F(), " ";
  print c.G(), " ";
  u := c.M();
  print u, " ";
  u := c.N();
  print u, "\n";

  print t.b, " ";
  print t.c, " ";
  print t.d, " ";
  print t.e, " ";
  print t.F(), " ";
  print t.G(), " ";
  u := t.M();
  print u, " ";
  u := t.N();
  print u, "\n";

  print i.b, " ";
  print i.c, " ";
  print i.d, " ";
  print i.e, " ";
  print i.F(), " ";
  print i.G(), " ";
  u := i.M();
  print u, " ";
  u := i.N();
  print u, "\n";

  // static members via type name

  print MyClass.d, " ";
  print MyClass.e, " ";
  print MyClass.G(), " ";
  u := MyClass.N();
  print u, "\n";

  print MyClass.d, " ";
  print MyClass.e, " ";
  print MyClass.G(), " ";
  u := MyClass.N();
  print u, "\n";

  print MyClass.d, " ";
  print MyClass.e, " ";
  print MyClass.G(), " ";
  u := MyClass.N();
  print u, "\n";
}


method TestMyClass()
{
  var c := new MyClass(3);
  var t := new MyClass(2);
  var i := new MyClass(2);
  print t == t, " ", i == i, " ", i == t, "\n";
  var t2 : MyClass := t;
  var t3 : MyClass;
  t3 := t;
  CallEm(c, t, i);
  c.stuffWithAr();
}


class AClass {
  var x:uint32;
  var y:uint32;

  constructor()
  {
    x := 0;
    y := 0;
  }
}

method TestEquality() {
  var a := new AClass();
  a.x := 25;
  a.y := 15;

  if a == a {
    print "EqualityReflexive: This is expected\n";
  } else {
    print "EqualityReflexive: This is unexpected\n";
    assert false;
  }

  var b := new AClass();
  b.x := 1;
  b.y := 2;

  if a == b {
    print "ClassAndPtrDiffer: This is unexpected\n";
    assert false;
  } else {
    print "ClassAndPtrDiffer: This is expected\n";
  }

  var c := new AClass();
  c.x := 25;
  c.y := 15;


  if a == c {
    print "DeepEquality: This is unexpected\n";
    assert false;
  } else {
    print "DeepEquality: This is expected\n";
  }
}

method Main() {
  TestMyClass();
  TestEquality();
}

