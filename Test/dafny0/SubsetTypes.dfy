// RUN: %exits-with 4 %dafny /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module AssignmentToNat {
  method M(x0: int, x1: int, x2: int, x3: int)
  {
    var a: nat := x0;  // error
    a := x1;  // error
    var z;
    z := var b: nat := x2; b;  // error
    z := var b: nat :| b == x3; b;  // error
  }
  method M'(x0: int, x1: int, x2: int, x3: int, x4: int)
  {
    var c: nat :| c == x0;  // error
    c :| c == x1;  // error

    var g := new G;
    g.u := x2;  // error

    var y := F(x3);  // error

    M''(x4);  // error
  }
  method M''(x: nat)

  function F(q: nat): int
  function F'(x: int): nat
  {
    F      // error (regarding result of F(x))
      (x)  // error (regaring argument to F)
  }

  class G {
    var u: nat
  }

  function Pf(n: nat): int
  function Pg(x: int): nat

  method P(x: int, f: nat ~> int) returns (g: int ~> nat)
    requires f.requires(x)  // error
  {
    var y := f(x);  // error
  }
  method Q(x: int) {
    var f := Pf;
    var g := Pg;
    var a := f(x);  // error
    var id := (u: int) => u;
    g := id;  // error
  }

  ghost function Id(x: int): nat
  {
    x  // error
  }
}

module AssignmentToSetNat {
  method M(x0: set<int>, x1: set<int>, x2: set<int>, x3: set<int>)
  {
    var a: set<nat> := x0;  // error
    a := x1;  // error
    var z;
    z := var b: set<nat> := x2; b;  // error
    z := var b: set<nat> :| b == x3; b;  // error
  }
  method M'(x0: set<int>, x1: set<int>, x2: set<int>, x3: set<int>, x4: set<int>)
  {
    var c: set<nat> :| c == x0;  // error
    c :| c == x1;  // error

    var g := new G;
    g.u := x2;  // error

    var y := F(x3);  // error

    M''(x4);  // error
  }
  method M''(x: set<nat>)

  function F(q: set<nat>): set<int>
  function F'(x: set<int>): set<nat>
  {
    F      // error (regarding result of F(x) in the body)
      (x)  // error (regaring argument to F)
  }

  class G {
    var u: set<nat>
  }

  function Pf(n: set<nat>): set<int>
  function Pg(x: set<int>): set<nat>

  method P(x: set<int>, f: set<nat> ~> set<int>) returns (g: set<int> ~> set<nat>)
    requires f.requires(x)  // error
  {
    var y := f(x);  // error
    g := z => z;  // error
  }
  method Q(x: set<int>) {
    var f := Pf;
    var g := Pg;
    var a := f(x);  // error
    var id := u => u;
    g := id;  // error
  }

  ghost function Id(x: set<int>): set<nat>
  {
    x  // error
  }
}

module OutParameters {
  method P<T>(x: T) returns (y: T) { y := x; }

  method M() returns (x: int, n: nat) {
    if {
      case true =>  x := P<nat>(n);
      case true =>  n := P<nat>(x);  // error (x)
      case true =>  x := P<int>(n);
      case true =>  n := P<int>(x);  // error (n)
    }
  }
}

module Contravariance {
  method M0(a: int ~> int, b: int ~> nat, c: nat ~> int, d: nat ~> nat) returns (r: int ~> int) {
    if {
      case true =>  r := a;
      case true =>  r := b;
      case true =>  r := c;  // error
      case true =>  r := d;  // error
    }
  }
  method M1(a: int ~> int, b: int ~> nat, c: nat ~> int, d: nat ~> nat) returns (r: int ~> nat) {
    if {
      case true =>  r := a;  // error
      case true =>  r := b;
      case true =>  r := c;  // error
      case true =>  r := d;  // error
    }
  }
  method M2(a: int ~> int, b: int ~> nat, c: nat ~> int, d: nat ~> nat) returns (r: nat ~> int) {
    if {
      case true =>  r := a;
      case true =>  r := b;
      case true =>  r := c;
      case true =>  r := d;
    }
  }
  method M3(a: int ~> int, b: int ~> nat, c: nat ~> int, d: nat ~> nat) returns (r: nat ~> nat) {
    if {
      case true =>  r := a;  // error
      case true =>  r := b;
      case true =>  r := c;  // error
      case true =>  r := d;
    }
  }
}

module AssignSuchThat {
  type SmallInt = x | 0 <= x < 10
  method M() {
    var a: int :| a == 11;
    var b: SmallInt :| b == 11;  // error
  }
}

module SoftCasts {
  method P(n: nat) returns (g: int ~> nat)
  {
    if
    case true =>
      g := z => (if z < 0 then -z else z) as nat; // OK with check in verifier
    case true =>
      g := z => if z <= 0 then -z else z-1; // OK with check in verifier
    case true =>
      g := (z: int) => if z < 0 then -z else z-1;  // error: may fail to return a nat
    case true =>
      g := z => n;
  }
}

module AssignmentsFromNewAllocation {
  // Many of the tests in this module are regression tests
  class Person { }
  class Cell<T> { }

  method J(N: nat, p: Person) {
    var a: array<Person?>;
    var b: array<Person>;
    if * {
      var c;
      c := new Person[0](_ => null);  // fine
      c := new Person[1](_ => null);  // error: null is not a Person
    }
    a := new Person?[N](_ => p);
    a := new Person?[N](_ => null);
    b := new Person[N](_ => p);
    b := new Person[N](_ => null);  // error: null is not a Person
  }

  method N(p: Person) returns (a: array<Person>, b: array<Person?>)
  {
    var c := new Person[1] [p];
    var d := new Person?[1];
    if * {
      a := c;
      b := c;  // error: arrays are non-variant
    } else if * {
      b := d;
      a := d;  // error: arrays are non-variant
    }
  }

  // unlike array, seq is co-variant in its argument type
  method O(p: Person) returns (a: seq<Person>, b: seq<Person?>)
  {
    var c: seq<Person> := [p];
    var d: seq<Person?> := [p];
    var e: seq<Person?> := [null];
    if * {
      assume |b| == 0;
      a := b;  // fine, given the previous line
    } else if * {
      b := a;
    } else if * {
      a := b;  // error
    } else if * {
      a := c;
      b := c;
    } else if * {
      b := d;
      a := d;
    } else if * {
      b := e;
      a := e;  // error
    }
  }

  method P(cc: Cell<Person?>, dd: Cell<Person>)
  {
    var c: Cell<Person?>;
    var d: Cell<Person>;
    if * {
      c := new Cell<Person?>;
    } else if * {
      d := new Cell<Person>;
    }
  }
}

module RegressionsSubsetElementTypes {
  type byte = x | 0 <= x < 256

  datatype Dt =
    | One(byte)
    | Many(seq<byte>)
    | Sany(set<byte>)
    | Bany(multiset<byte>)
    | Pany(map<byte,byte>)

  method M0() returns (dt: Dt)
  {
    if
    case true =>  dt := One(500);  // error
    case true =>  dt := Many([500]);  // error
    case true =>  dt := Sany({500});  // error
    case true =>  dt := Bany(multiset{500});  // error
  }
  method M1() returns (dt: Dt)
  {
    if
    case true =>  dt := Pany(map[500 := 20]);  // error
    case true =>  dt := Pany(map[20 := 500]);  // error
  }
  method M2(x: int, s: seq<int>, t: set<int>, u: multiset<int>, m: map<int,int>) returns (dt: Dt)
  {
    if
    case true =>  dt := One(x);  // error
    case true =>  dt := Many(s);  // error
    case true =>  dt := Sany(t);  // error
    case true =>  dt := Bany(u);  // error
    case true =>  dt := Pany(m);  // error
  }
  method M3(s: seq<int>, t: set<int>, u: multiset<int>, m: map<int,int>) returns (dt: Dt)
  {
    if
    case true =>
    case forall i :: 0 <= i < |s| ==> 0 <= s[i] < 256 =>
      dt := Many(s);
    case forall x :: x in t ==> 0 <= x < 256 =>
      dt := Sany(t);
    case forall x :: x in u ==> 0 <= x < 256 =>
      dt := Bany(u);
    case forall x :: x in m.Keys ==> 0 <= x < 256 && 0 <= m[x] < 256 =>
      dt := Pany(m);
  }

  method M4(dm: Dt) returns (x: int, s: seq<int>, t: set<int>, u: multiset<int>, m: map<int,int>)
  {
    match dm
    case One(a) =>  x := a;
    case Many(b) =>  s := b;
    case Sany(c) =>  t := c;
    case Bany(d) =>  u := d;
    case Pany(e) =>  m := e;
  }
}

// ----------- regression tests, make sure RHS's of const's are checked ----------

module RegressionConstWithRhsAndConstraints0 {
  const x: nat := -1  // error: RHS does not satisfy subtype type of const
}

module RegressionConstWithRhsAndConstraints1 {
  class C {
    const x: nat := -1  // error: RHS does not satisfy subtype type of const
  }
}

module RegressionConstWithRhsAndConstraints2 {
  newtype Nat = x | 0 <= x
  const x: Nat := -1  // error: RHS does not satisfy newtype type of const
}

module RegressionConstWithRhsAndConstraints3 {
  newtype Nat = x | 0 <= x
  class C {
    const x: Nat := -1  // error: RHS does not satisfy newtype type of const
  }
}

module RegressionUninhabited0 {
  type Nat = x: int | false  // error: type is uninhabited
  const x: Nat := -1  // error: RHS does not satisfy constraint
}

module RegressionUninhabited1 {
  newtype Nat = x: int | false  // error: type is uninhabited
  const x: Nat := -1  // error: RHS does not satisfy constraint
}

module Uninhabited2 {
  type Nat = x: int | false  // error: type is uninhabited
  method M() returns (r: Nat)
  {
    assert false;  // unreachable, since Nat is uninhabited
  }
}

module RegressionIllformedConstRhs0 {
  const x: int := 15 / 0  // error: division by zero
}

module RegressionIllformedConstRhs1 {
  class C {
    const x: int := 15 / 0  // error: division by zero
  }
}

module ErrorMessagesOfFailingConstraints {
  type X = u | u % 2 == 0  // multiples of 2
  type Y = v: X | v % 3 == 0  // multiples of 6
  class C { }

  method M0(x: int, c: C?) {
    if
    case true =>
      var xx: X := x;  // error: x may be odd
    case true =>
      var yy: Y := x;  // error: x may not be a multiple of 6
    case x % 3 == 0 =>
      var yy: Y := x;  // error: x may be odd
    case x % 2 == 0 =>
      var yy: Y := x;  // error: x may not be a multiple of 3
    case true =>
      var cc: C := c;  // error: c may be null
  }
  method M1(f: int ~> int, g: int --> int) {
    if
    case true =>
      var ff: int --> int := f;  // error: f may have read effects
    case true =>
      var gg: int -> int := g;  // error: g may be partial
    case true =>
      var gg: int -> int := f;  // error: f may have read effects or be partial
    case true =>
      var hh: int ~> nat := f;  // error: f may return negative numbers
    case true =>
      var hh: int ~> X := f;  // error: f may return odd numbers
  }
  method m2(x: int) returns (n: nat) {
    n := x;  // error: x may be negative
  }
}

// ----------- regression tests, subset type of char ----------

module CharSubsetDefault {
  // If a witness clause is not given, then value the verifier uses 'D' as the
  // candidate witness for char. This value must agree with what the compilers do.
  type GoodChar = ch: char | 3 as char < ch < 200 as char
  type NeedsWitnessChar0 = ch: char | ch < 40 as char  // error: needs manually provided witness
  type GoodWitness0 = ch: char | ch < 40 as char witness ' '
  type NeedsWitnessChar1 = ch: char | ch != 'D'  // error: needs manually provided witness
  type GoodWitnessChar1 = ch: char | ch != 'D' witness 'd'
}

// ----------- regression tests, eagerly assigning the type to the bound variable ----------

module EagerTypeAssignmentOfBoundVariables {
  // In the following, "MatchPattern" and "MatchIt0" previously ended up inferring the
  // type of "n - 10" as "nat", which causes an additional (and unwanted) error saying that
  // the result of "n - 10" is not a "nat". This has now been fixed (but see also Issue #1263).

  datatype Record = Record(nat)

  method MatchPattern(r: Record)
  {
    var Record(n) := r;
    assert 0 == n - 10;  // error: possible assertion failure
  }

  method MatchIt0(r: Record)
  {
    match r
    case Record(n) =>
      assert 0 <= n - 10;  // error: possible assertion failure
  }

  type MyNat = nat

  method MatchIt1(r: Record)
  {
    match r
    case Record(n: nat) =>
      assert 0 <= n - 10;  // error: possible assertion failure
  }

  method MatchIt2(r: Record)
  {
    match r
    case Record(n: int) =>
      assert 0 <= n - 10;  // error: possible assertion failure
  }

  method MatchIt3(r: Record)
  {
    match r
    case Record(n: MyNat) =>
      assert 0 <= n - 10;  // error: possible assertion failure
  }

  method Minus(n: nat)
  {
    assert 0 <= n - 10;  // error: possible assertion failure
  }
}
