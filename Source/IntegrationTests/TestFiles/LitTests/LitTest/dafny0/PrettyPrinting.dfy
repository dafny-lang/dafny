// RUN: %exits-with 2 %build --print:- --no-verify "%s" > "%t"
// RUN: %exits-with 2 %build --print:- --no-verify --type-system-refresh "%s" > "%t.refresh"
// RUN: %diff "%s.expect" "%t"
// RUN: %diff "%s.expect" "%t.refresh"

module A {
  method M()
}

module B refines A {
  method M ... {
    while true
    while true
      invariant true
      invariant true
    while true
      decreases 5
    while true
      modifies {}
    while ...
    while true
      ...
    while true {
      var u := 0;
    }
    var x := 10;
  }

  method P(a: array<int>)
    modifies a
  {
    forall i | 0 <= i < 100 {
      a[i] := 200;
    }
    forall i | 0 <= i < 100
      ensures true
    forall i | 0 <= i < 100
      ensures true
    {
    }
  }
}

module C {
  method For() {
    ghost var (x, y) := (123, 234);
    var a := new int[100];
    for i := 0 to 100 {
      a[i] := i;
    }
    for i := 100 downto 0 {
      a[i] := i;
    }
    for i: nat := 0 to 100
    for i: nat := 100 downto 0
    for i := 0 to 100
      invariant a[5] == 5
      invariant a[12] == 12
    for i := 100 downto 0
      invariant a[5] == 5
    for i := 0 to 100
      invariant a[5] == 5
      invariant a[12] == 12
    {
    }
    for i := 100 downto 0
      invariant a[5] == 5
    {
      assert true;
    }
    for i := 0 to *
      decreases 100 - i
      invariant i <= 100
    for i := 0 to *
      decreases *
    {
    }
    var c := new Cell;
    for i := 0 to 100
      modifies c
      modifies {c}, {c}
    {
    }
    for i := 100 downto *
      modifies c
      decreases i
      modifies {c}, {c}
      invariant -68 <= i <= 68
      invariant i != 3
    {
    }
  }
  class Cell { var data: int }
}

module Ats {
  class Cell {
    var data: int

    method M()
    {
      label Label:
      assert old(data) == old@Label(data);
      assert unchanged(this) && unchanged@Label(this);
      var c := new Cell;
      assert fresh(c) && fresh@Label(c);
    }
  }
}

module ByMethod {
  function F(x: nat): int {
    x
  } by method {
    var j := 0;
    for _ := 0 to x {
      j := j - 1;
    }
    return -j;
  }
}

module GhostConstructors {
  class C {
    constructor X()
    ghost constructor Y()
  }
}

module BreakContinue {
  method M() {
    label Outer:
    for i := 0 to 100 {
    label Inner:
      for j := 0 to 100 {
        label X: {
          label Innerer:
          for k := 0 to 100 {
            if
            case true => break;
            case true => continue;
            case true => break break;
            case true => break continue;
            case true => break break break;
            case true => break break continue;
            case true => break Innerer;
            case true => break Inner;
            case true => break Outer;
            case true => break X;
            case true => continue Innerer;
            case true => continue Inner;
            case true => continue Outer;
          }
        }
      }
    }
  }
}

module New {
  method M() {
    var three := 3;
    var a;
    a := new int[3] [20, 50, 70];
    a := new [3] [20, 50, 70];
    a := new [three] [20, 50, 70];
    a := new int[] [20, 50, 70];
    a := new [] [20, 50, 70];
  }
}

module BoundedPolymorphism {
  trait Trait { }

  datatype DT<W extends Trait> = Dt(w: W)

  type Syn<X extends Trait> = DT<X>

  class Class<Y extends Trait> {
  }

  trait AnotherTrait<Z extends Trait> {
  }

  type Abstract<V extends Trait extends AnotherTrait<Trait>>

  trait Generic<Q> { }

  codatatype Mutual<A extends Generic<B>, B extends Generic<A>> = More(Mutual)

  function Function<K extends Trait>(k: K): int { 2 }

  method Method<L extends Trait>(l: L) { }

  least predicate Least<M extends Trait>(m: M) { true }

  greatest lemma Greatest<N extends Trait>(n: N) { }

  iterator Iter<O extends Trait>(o: O) { }
}

module SimpleNewtypeWitness {
  newtype A = x: int | 100 <= x witness 102
  newtype B = a: A | true witness 103

  newtype C = A
  newtype D = A witness 104
  newtype E = A ghost witness 104
  newtype F = A witness *
}

module DecreasesTo {
  lemma Lemma(x: int) {
  }

  datatype Record = R

  ghost method ParseAndPrettyPrintTests(b: bool)
    ensures (Lemma(0); true)

    ensures (if b then Lemma(0); true else Lemma(0); true)
    ensures if b then Lemma(0); true else (Lemma(0); true)

    ensures (Lemma(0); b <==> b) // Lemma(0) comes before <==> expression
    ensures (Lemma(0); (b <==> b)) // same as above
    ensures ((Lemma(0); b) <==> (Lemma(1); b))

    ensures (Lemma(0); true decreases to (Lemma(1); false)) // Lemma(0) comes before the entire decreases-to
    ensures (Lemma(0); true, Lemma(1); true decreases to (Lemma(2); false)) == (true, true) // Lemma(1) comes before the entire decreases-to
    ensures (true, Lemma(0); true decreases to (Lemma(1); false)) == (true, true) // Lemma(0) comes before the entire decreases-to
    ensures (Lemma(0); R, Lemma(0); true) decreases to (Lemma(0); R)
    ensures (Lemma(0); true) decreases to (Lemma(0); false)
  {
    while Lemma(0); false  {
    }
    while if b then Lemma(0); false else Lemma(0); false
    {
    }
    while (Lemma(0); false decreases to (Lemma(1); false))
    {
    }
    while (Lemma(0); R, Lemma(0); true) decreases to (Lemma(0); 15)
    {
    }
    while (Lemma(0); true) decreases to (Lemma(0); 15)
    {
    }
  }
}
