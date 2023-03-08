// RUN: %dafny /env:0 /dprint:"%t.dfy" /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


module A {
  export Specf provides T, f
  export Bodyg provides T, g

  export SpecF provides T, F
  export BodyG provides T, G

  type T = T2
  datatype T2 = C(x: T2) | N

  ghost function f(x: T, y: int): T { if y <= 0 then x else f(x, y-1) }

  ghost function g(x: T): T
   decreases x
   { match x
     case C(x') => g(x')
     case N => x
   }

  method F(x: T, y: int) {
    if (y > 0) {
       F(x, y-1);
    }

  }

  method G(x: T)
  decreases x
  {
    match (x) {
       case C(x') =>
            G(x');
       case N =>
           assert true;
    }
  }

}

module B {
  import A`Specf

  ghost function h(x: A.T): A.T { A.f(x, 1) }
}

module C {
  import A`Bodyg
  ghost function i(x: A.T): A.T { A.g(x) }
}

module D {
  import A`SpecF

  method H(x: A.T) {
     A.F(x, 2);
  }
}

module E {
  import A`BodyG

  method I(x: A.T) {
    A.G(x);
  }

}



