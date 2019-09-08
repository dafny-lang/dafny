newtype{:nativeType "uint"} uint32 = i:int | 0 <= i < 0x100000000

class MyClass {
  var a: uint32
  const b: uint32
  const c:uint32 := 17
  static const d: uint32
  static const e:uint32 := 18
  constructor (x: uint32) 
    requires x < 100;
    ensures this.a < 300;
    ensures this.b < 300;
  {
    a := 100 + x;
    b := 200 + x;
  }

  function method F(): uint32 { 8 }
  static function method G(): uint32 { 9 }
  method M() returns (r: uint32) { r := 69; }
  static method N() returns (r: uint32) { return 70; }
}

method CallEm(c: MyClass, t: MyClass, i: MyClass)
  requires c.a as int + t.a as int + i.a as int < 1000;
  modifies c, t, i
{
  /*
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
  */
  print c.d, " ";
  /*
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
  */
  var u := MyClass.N();
  print u, "\n";
}

method Main() {
  var c := new MyClass(3);
  var t := new MyClass(2);
  var i := new MyClass(2);
  print t == t, " ", i == i, " ", i == t, "\n";
  var t2 : MyClass := t;
  var t3 : MyClass;
  t3 := t;
  CallEm(c, t, i);
}

