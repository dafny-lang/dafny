// RUN: %testDafnyForEachResolver "%s" -- --rprint:- --relax-definite-assignment


module M0 {
  trait Tr<X> {
    ghost function F(x: X): int { 15 }
  }

  class Cl<Y> extends Tr<Y> {
    lemma M() {
      var v := this;  // Cl<Y>
      var u: Tr := this;  // Tr<Y>

      var f := v.F;  // Y -> int
      var g := this.F;  // Y -> int
    }
  }
}

module M1 {
  trait Tr<X(0)> extends object {
    var w: X
  }

  class Cl<Y(0)> extends Tr<(Y,Y)> {
  }

  lemma M(c: Cl<int>) {
    var x := c.w;  // (int, int)
  }
}

module M2 {
  trait Tr<X, W> {
    function F(x: X, w: W): bv10 { 15 }
  }

  class Cl<Y> extends Tr<(Y,Y), real> {
  }

  lemma M(c: Cl<int>) {
    var aa;  // (int, int)
    var bb;  // real
    var u := c.F(aa, bb);  // bv10
  }
}

module M3 {
  trait Tr<X(0)> {
    const w: X // const in non-reference trait
  }

  class Cl<Y(0)> extends Tr<(Y,Y)> {
  }

  lemma M(c: Cl<int>) {
    var x := c.w;  // (int, int)
  }
}

module M4 {
  trait Tr<X(0)> extends object {
    const w: X // const in reference trait
  }

  class Cl<Y(0)> extends Tr<(Y,Y)> {
  }

  lemma M(c: Cl<int>) {
    var x := c.w;  // (int, int)
  }
}

module P0 {
  trait TrX<X> {
    ghost function F(x: X): int { 15 }
  }

  trait Tr<X> extends TrX<X> {
  }

  class Cl<Y> extends Tr<Y> {
    lemma M() {
      var v := this;  // Cl<Y>
      var u: Tr := this;  // Tr<Y>

      var f := v.F;  // Y -> int
      var g := this.F;  // Y -> int
    }
  }
}

module P1 {
  trait TrX<X(0)> extends object {
    var w: X
  }

  trait Tr<X(0)> extends TrX<X> {
  }

  class Cl<Y(0)> extends Tr<(Y,Y)> {
  }

  lemma M(c: Cl<int>) {
    var x := c.w;  // (int, int)
  }
}

module P2 {
  trait TrX<X, W> {
    function F(x: X, w: W): bv10 { 15 }
  }

  trait Tr<X, W> extends TrX<X, W> {
  }

  class Cl<Y> extends Tr<(Y,Y), real> {
  }

  lemma M(c: Cl<int>) {
    var aa;  // (int, int)
    var bb;  // real
    var u := c.F(aa, bb);  // bv10
  }
}
