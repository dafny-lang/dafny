// RUN: %testDafnyForEachCompiler "%s" -- --type-system-refresh --general-traits=datatype

method Main() {
  As.Test();
  Is.Test();
  Basic.Test();
  Bounds.Test();
}

module As {
  trait Parent {
    const k: int
  }
  trait Trait extends Parent { }
  class Class extends Trait {
    constructor (n: int) {
      k := n;
    }
  }

  method Test() {
    var c := new Class(14);
    M(c);
    var b := N(c);
    O(c);
    P(c);
  }
  
  method M<X extends Trait>(x: X) {
    var a0 := x as X;
    var a1 := x as Trait;
    var a2 := x as Parent;
    print a1.k, " "; // 14
  }

  method N<X(==) extends Trait>(x: X) returns (b: bool) {
    var t: Trait := x as Trait;
    b := x == t as X;
    print b, " "; // true
  }

  method O<Z extends object?>(z: Z) {
    var a := z as object?;
    print a != null, " "; // true
  }

  method P<Z extends object>(z: Z) {
    var a := z as object?;
    var b := z as object;
    print b == a != null, "\n"; // true
  }
}

module Is {
  trait Parent {
    const k: int
  }
  trait Trait extends Parent { }
  class Class extends Trait {
    constructor (n: int) {
      k := n;
    }
  }

  method Test() {
    var c := new Class(14);
    M(c);
    O(c); // true true
    O(null); // true false
    P(c);
  }
  
  method M<X extends Trait>(x: X) {
    print x is X, " "; // true
    print x is Trait, " "; // true
    print x is Parent, " "; // true
    print (x as Trait) is Class, "\n"; // false
  }

  method O<Z extends object?>(z: Z) {
    print z is object?, " ";
    print z is object, " ";
  }

  method P<Z extends object>(z: Z) {
    print z is object?, " "; // true
    print z is object, "\n"; // true
  }
}

module Basic {
  trait Parent extends object {
    const k: int
  }
  trait Trait extends Parent { }
  class Class extends Trait {
    constructor (n: int) {
      k := n;
    }
  }

  method TestMethod<X extends Trait? extends Parent>(x: X) returns (obj: object?)
    ensures obj != null
  {
    var b := x is Trait;
    assert b;
    print b, " "; // true

    b := x is Parent;
    assert b;
    print b, " "; // true

    var t: Trait := x as Trait;
    obj := t;
  }

  method Test() {
    var c := new Class(18);
    var obj := TestMethod(c);
    print obj != null, "\n"; // true
  }
}

module Bounds {
  trait Trait<X> {
    function Value(): X
  }

  datatype Dt extends Trait<string> = Dt(s: string)
  {
    function Value(): string { s }
  }

  method MyMethod<Y extends Trait<string>>(y: Y) {
    var s := (y as Trait<string>).Value();
    print "(", s, ")\n";
  }

  class RandomClass<R> extends Trait<R> {
    const r: R
    constructor (r: R) {
      this.r := r;
    }
    function Value(): R { r }
  }

  method Test() {
    var d := Dt("hello");
    MyMethod(d);

    var c := new RandomClass("you don't say");
    MyMethod(c);

    var v := *; // inferred to be of type string (pretty cool, huh!)
    var i := new RandomClass(v);
    MyMethod(i);
  }
}
