// RUN: %testDafnyForEachCompiler "%s" -- --general-traits

method Main() {
  BoxingConcerns.Test();
  RefAndBoxConversions.Test();
  print "done\n";
}

module BoxingConcerns {
  trait Parent { }
  class Class extends Parent { }

  method M(c: Class) {
    var a: Parent;
    var b: Parent;
    a, b := c, c;
  }

  class Generic<X> {
    var x: X
    constructor (x: X) {
      this.x := x;
    }
  }

  method P(g: Generic<int>)
    modifies g
  {
    var y: int, z: int;
    y, z := g.x, g.x;

    g.x, g.x := y, z;
  }

  method Q(h: Generic<Parent>, cl: Class)
    modifies h
  {
    h.x, h.x := cl, cl;
  }

  method Test() {
    var c := new Class;
    M(c);
    var gi := new Generic<int>(5);
    P(gi);
    var gp := new Generic<Parent>(c);
    Q(gp, c);
  }
}

module RefAndBoxConversions {
  trait Parent {
    const aa: int
  }

  trait RefParent extends object {
    var bb: int
  }

  class Class extends Parent, RefParent {
  }

  class ClassWithConstructor extends Parent, RefParent {
    constructor () {
      aa := 14;
      bb := 15;
    }
  }

  newtype MyInt extends Parent = x | -0x8000_0000 <= x < 0x8000_0000

  method Test0(u: bool) returns (p: Parent, q: RefParent, r: RefParent?) {
    if u {
      var x := new Class;
      return x, x, x;
    } else {
      var x := new ClassWithConstructor();
      return x, x, x;
    }
  }

  method Test1(u: bool) returns (p: Parent, q: RefParent, r: RefParent?) {
    if u {
      var x: Class := new Class;
      return x, x, x;
    } else { 
      var x: ClassWithConstructor := new ClassWithConstructor();
      return x, x, x;
    }
  }

  method Test2(u: bool) returns (p: Parent, q: RefParent, r: RefParent?) {
    if u {
      var x: Class? := new Class;
      return x, x, x;
    } else {
      var x: ClassWithConstructor? := new ClassWithConstructor();
      return x, x, x;
    }
  }

  method Test() {
    var p, q, r;
    p, q, r := Test0(true);
    Print(p, q, r);
    p, q, r := Test0(false);
    Print(p, q, r);
    p, q, r := Test1(true);
    Print(p, q, r);
    p, q, r := Test1(false);
    Print(p, q, r);
    p, q, r := Test2(true);
    Print(p, q, r);
    p, q, r := Test2(false);
    Print(p, q, r);
    var n: MyInt := 200;
    print n, " ", n.aa, "\n";
  }

  method Print(p: Parent, q: RefParent, r: RefParent?) {
    print p.aa, " ";
    print q.bb, " ";
    if r == null {
      print "null";
    } else {
      print r.bb;
    }
    print "\n";
  }
}
