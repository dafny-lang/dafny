// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Cycle {
  type MySynonym = MyNewType  // error: a cycle
  newtype MyNewType = MyIntegerType_WellSupposedly
  type MyIntegerType_WellSupposedly = MySynonym
}

module MustBeNumeric {
  datatype List<T> = Nil | Cons(T, List)
  newtype NewDatatype = List<int>  // error: base type must be numeric based
}

module Goodies {
  newtype int32 = int
  newtype posReal = real
  newtype int8 = int32

  method M()
  {
    var k8 := new int8[100];
    var s: set<int32>;
    var x: posReal;
    var y: posReal;
    var z: int32;
    x := 5.3;
    z := 12;
    s := {};
    s := {40,20};
    x := x + y;
    var r0 := x as real;
    var r1: real := 2.0 * r0;
    var i0 := z as int;
    var i1: nat := 2 * i0;
    assert i1 == 24;
    assert r1 == 10.6;
    if x == r0 {  // error: cannot compare posReal and real
    } else if x as real == r0 {
    } else if i0 == x as int {
    } else if i0 == x as real as int {
    } else if i0 as real == x as real {
    }
    if z == i0 {  // error: cannot compare int32 and int
    } else if z as int == i0 {
    } else if r0 == z as real {
    } else if r0 == z as int as real {
    } else if r0 as int == z as int {
    }
    assert x == z;  // error: cannot compare posReal and int32
    assert x <= z;  // error: cannot compare posReal and int32
    assert z < i0;  // error: cannot compare int32 and int
    assert x > r1;  // error: cannot compare posReal and real

    var di := z % 2 - z / 2 + if z == 0 then 3 else 100 / z + 100 % z;
    var dr := x / 2.0 + if x == 0.0 then 3.0 else 100.0 / x;
    dr := dr % 3.0 + 3.0 % dr;  // error (x2): mod not supported for real-based types
    z, x := di, dr;

    var sq := [23, 50];
    assert forall ii :: 0 <= ii < |sq| ==> sq[ii] == sq[ii];
    var ms := multiset{23.0, 50.0};
    assert forall rr :: 0.0 <= rr < 100.0  ==> ms[rr] == ms[rr];

    var floored := r0.Floor + x.Floor;
    var rounded := (r0 + 0.5).Floor;
  }
}

module Constraints {
  newtype SmallInt = x: int | 0 <= x < 100
  newtype LargeInt = y: int | 0 <= y < 100

  newtype BadConstraint = a: SmallInt
    | a + a  // error: not a boolean
  newtype WotsDisVariable = u  :BadConstraint
    | u + a < 50  // error: undeclared identifier 'a'

  newtype A = x: int | 0 <= x
  newtype B = x: A | x < 100
  newtype C = B  // the constraints 0 <= x < 100 still apply

  predicate IsEven(x: int)  // note that this is a ghost predicate
  {
    x % 2 == 0
  }
  newtype G = x: int | IsEven(x)  // it's okay to use ghost constructs in type constraints

  newtype N = nat

  newtype OldState = y: real | old(y) == y  // error: old is not allowed in constraint

  newtype AssertType = s: int |
    var k := s;
    assert k == s;
    k < 10 || 10 <= s
}

module WrongNumberOfArguments {
  newtype N = nat
  method BadTypeArgs(n: N<int>)  // error: N takes no type arguments
}

module CyclicDependencies {
  newtype Cycle = x: int | (BadLemma(); false)  // error: cycle
  lemma BadLemma()
    ensures false;
  {
    var c: Cycle;
  }
}

module SelfCycleTest {
  newtype SelfCycle = x: int | var s: SelfCycle := 4; s < 10  // error: cyclic dependency on itself
}

module Module0 {
  import Module1
  method M(x: int) returns (n: Module1.N9) {
    var x := Module1.N9;  // error
  }
}

module Module1 {
  newtype N9 = int
}

module InferredType {
  newtype Int = x | 0 <= x < 100
  newtype Real = r | 0.0 <= r <= 100.0
  method M() returns (i: Int, r: Real)
  {
    i := 4;
    r := 4.0;
  }
  newtype AnotherInt = int
  method P(i: int, a: AnotherInt) returns (j: Int)
  {
    j := i;  // error: int not assignable to Int
    j := a;  // error: AnotherInt not assignable to Int
  }
}

module SynonymsAndModules {
  module M {
    type Syn = int
    type Y = Klass
    class Klass {
      static method H()
    }
  }

  method P()
  {
    var x: M.Syn;
    x := B;  // error: bad use of B
    x := M.Syn;  // error: bad use of M.Syn
    C.D();
    X.D();
    M.Klass.H();
    M.Y.H();
    M.Y.U();  // error: non-existent member U
  }

  type B = int
  type X = C
  class C {
    static method D()
  }
}

module MoreSynonyms {
  import SynonymLibrary

  type Syn<T> = Syn'<T,T>
  type Syn'<A,B> = C<B>
  class C<alpha> {
    static method MyMethod<beta>(b: beta, a: alpha)
  }
  method M() {
    var a, b;
    Syn.MyMethod(b, a);
    a, b := 25, true;
  }
  method P() {
    var d := SynonymLibrary.S.Cons(50, SynonymLibrary.Dt.Nil);
    var e := SynonymLibrary.Dt.Cons(true, SynonymLibrary.S.Cons(40, d));
    var f := SynonymLibrary.S.Cons(50, SynonymLibrary.S.Cons(true, d));  // error: 'true' argument is expected to be an integer
  }
}

module SynonymLibrary {
  type S = Dt<int>
  datatype Dt<T> = Nil | Cons(T, S)
}

module QualifiedDatatypeCtor {
  type S = Dt<int>
  datatype Dt<T> = Nil | Cons(T, S)

  method P() {
    var d: S;
    var f := S.Cons(50, S.Nil);
  }
}

module IntegerBasedValues {
  type T

  newtype Even = x | x % 2 == 0

  method Arrays(n: nat, o: Even, i: Even) returns (x: T)
    requires 0 <= o;
    requires -1 < i;  // note, -1 is not of type Even, but that's for the verifier (not type checker) to check
  {
    var a := new T[n];
    var b := new T[o];
    var m := new T[o, n];
    var m' := new T[o, n, 3.14];  // error: 3.14 is not of an integer-based type
    if {
      case i < n =>  // error: i and n are of different integer-based types
        x := a[i];
      case i < a.Length =>  // error: i and a.Length are of different integer-based types
        x := a[i];
      case i < o =>
        x := b[i];
      case i < b.Length =>  // error: i and b.Length are of different integer-based types
        x := b[i];
      case i < m.Length0 =>  // error: i and m.Length0 are of different integer-based types
      case i < m.Length1 =>  // error: i and m.Length1 are of different integer-based types
    }
  }

  method Sequences(a: seq<T>, i: Even) returns (x: T, b: seq<T>)
    requires 0 <= i;
  {
    if {
      case i < |a| =>  // error: i and |a| are of different integer-based types
        x := a[i];
      case i <= |a| as int =>  // error: type of i is a different integer-based type than int
        b := a[0..i];
    }
  }

  method MultisetUpdate<U>(m: multiset<U>, t: U, n: Even)
  {
    var m' := m[t := n];
    m' := m[t := 12];
    m' := m[t := 1.1415];  // error: real is not an integer-based numeric type
  }
}

module CompilableWitnesses {
  type XX = c: bool | true
    witness
      ghost var g := false; g  // error: witness must be compilable
  newtype XX' = c: int | true
    witness
      ghost var g := 0; g  // error: witness must be compilable
  type YY = c: bool | true
    witness
      forall x: int :: 0 <= x < 100  // error: witness must be compilable
  newtype YY' = c: int | true
    witness
      if forall x: int :: 0 <= x < 100 then 1 else 3  // error: witness must be compilable
}

module Regression {
  // The following are regression tests for what once had caused the resolver to crash
  type CC = c: bool | forall d: DD :: true
  type CC' = c: bool | false in set d: DD | true
  type DD = d: bool | true
}

module CycleViaConstraintsOrWitnesses {
  type AA = a: int | true witness var b: BB := 0; if b < 100 then 0 else 2  // error: cycle (AA, BB, CC, DD, EE)
  type BB = b: int | var a: CC := 0; a < 1
  type CC = c: int | forall d: DD :: d == d
  newtype DD = d: int | true witness var e: EE := 0; if e < 100 then 0 else 2
  newtype EE = e: int | var a: AA := 0; a < 1
}

module BigOrdinals {
  newtype MyOrdinal = ORDINAL  // error: cannot use ORDINAL here
  newtype MyOrdinal' = o: ORDINAL | true  // error: cannot use ORDINAL here
}

module Cycle0 {
  type X = x: int | P(x) // error: recursive constraint dependency

  predicate P(y: int) {
    M();
    true
  }

  lemma M() {
    var x: X;
  }
}

module Cycle1 {
  // regression: the following type synonym once foiled the recursive-constraint-dependency checking
  type X = Y
  type Y = x: int | P(x) // error: recursive constraint dependency

  predicate P(y: int) {
    M();
    true
  }

  lemma M() {
    var x: X;
  }
}

module Cycle2 {
  newtype X = x: int | P(x) // error: recursive constraint dependency

  predicate P(y: int) {
    M();
    true
  }

  lemma M() {
    var x: X;
  }
}

module Cycle3 {
  // regression: the following type synonym once foiled the recursive-constraint-dependency checking
  type X = Y
  newtype Y = x: int | P(x) // error: recursive constraint dependency

  predicate P(y: int) {
    M();
    true
  }

  lemma M() {
    var x: X;
  }
}

// ----- more tests of declaration dependencies

module LongerCycle0 {
  type G0 = G1
  type G1 = G2
  type G2 = G3<int>
  type G3<X> = p: (X, G5) | true witness * // error: recursive constraint dependency
  datatype G5 = G5(G6)
  codatatype G6 = G6(array<G0>)
}

module LongerCycle1 {
  type G0 = G1
  type G1 = G2
  type G2 = G3<int>
  type G3<X> = (X, G4)
  newtype G4 = x | 0 <= x < 5 && forall r :: P(r) ==> P(r) // error: recursive constraint dependency
  predicate P(r: G5)
  datatype G5 = G5(G6)
  codatatype G6 = G6(set<G0>)
}

module LongerCycle2 {
  type G0 = G1
  type G1 = G2
  type G2 = G3<int>
  type G3<X> = (X, G4)
  newtype G4 = x | 0 <= x < 5 && forall r :: P(r) ==> P(r) // error: recursive constraint dependency / illegally uses a reference type
  predicate P(r: G5)
  datatype G5 = G5(G6)
  codatatype G6 = G6(array<G0>)
}

// ----- regression

module CycleUnsoundnessRegression {
  type X = Y
  type Y = x: int | P(x) witness (M(); 2) // error: recursive constraint dependency

  predicate P(y: int) {
    false
  }

  lemma M()
    ensures false
  {
    var x: X;
    assert P(x);
  }
}

// ----- cycle through function-by-method's

module FunctionByMethod {
  // --- constraints

  newtype NT0 = x: int | P0(x)  // error: recursive dependency
  predicate P0(x: int) {
    x as NT0 == 3
  } by method {
    return x == 3;
  }

  newtype NT1 = x: int | P1(x)
  predicate P1(x: int) {
    x == 3
  } by method {
    return x as NT1 == 3;
  }

  type ST0 = x: int | Q0(x)  // error: recursive dependency
  predicate Q0(x: int) {
    x as ST0 == 3
  } by method {
    return x == 3;
  }

  type ST1 = x: int | Q1(x)
  predicate Q1(x: int) {
    x == 3
  } by method {
    return x as ST1 == 3;
  }

  // witnesses

  newtype NW0 = x: int | true ghost witness NWitness0()  // error: recursive dependency
  function NWitness0(): int {
    150 + (0 as NW0 as int)
  } by method {
    return 150;
  }

  newtype NW1 = x: int | true ghost witness NWitness1()
  function NWitness1(): int {
    150
  } by method {
    return 150 + (0 as NW1 as int);
  }

  newtype NW2 = x: int | true witness NWitness2()  // error: recursive dependency
  function NWitness2(): int {
    150 + (0 as NW2 as int)
  } by method {
    return 150;
  }

  newtype NW3 = x: int | true witness NWitness3()  // error: recursive dependency
  function NWitness3(): int {
    150
  } by method {
    return 150 + (0 as NW3 as int);
  }

  type SW0 = x: int | true ghost witness SWitness0()  // error: recursive dependency
  function SWitness0(): int {
    150 + (0 as SW0 as int)
  } by method {
    return 150;
  }

  type SW1 = x: int | true ghost witness SWitness1()
  function SWitness1(): int {
    150
  } by method {
    return 150 + (0 as SW1 as int);
  }

  type SW2 = x: int | true witness SWitness2()  // error: recursive dependency
  function SWitness2(): int {
    150 + (0 as SW2 as int)
  } by method {
    return 150;
  }

  type SW3 = x: int | true witness SWitness3()  // error: recursive dependency
  function SWitness3(): int {
    150
  } by method {
    return 150 + (0 as SW3 as int);
  }

  // constants

  ghost const c0 := R0()  // error: recursive dependency
  function R0(): int {
    2 + c0
  } by method {
    return 2;
  }

  const c1 := R1()  // error: recursive dependency
  function R1(): int {
    2 + c1
  } by method {
    return 2;
  }

  const c2 := R2()  // error: recursive dependency
  function R2(): int {
    2
  } by method {
    return 2 + c2;
  }
}
