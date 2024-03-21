// RUN: %testDafnyForEachCompiler "%s" -- --type-system-refresh --general-traits=datatype

method Main() {
  As.Test();
  Is.Test();
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
