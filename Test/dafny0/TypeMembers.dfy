// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  BasicTests();
  MoreTests();
}

// ---------- basic tests ----------

method BasicTests() {
  var t := Yes;
  var r := t.W();  // 10
  var q := t.Q() + DaTy.Q();  // 13 + 13
  print t, " ", r, " ", q, "\n";

  var p: Pos := 8; print p, " ";
  var u := Pos.Func(p); assert u == 11; print u, " ";
  var v := p.Gittit(); assert v == 10; print v, " ";
  var w := Pos.Method(p); assert w == 11; print w, " ";
  var x := p.Collect(); assert x == 10; print x, " ";
  print "\n";
}

datatype DaTy = Yes {
  function method W(): int { 10 }
  static function method Q(): int { 13 }
}

newtype Pos = x | 0 < x witness 1
{
  static function method Func(y: Pos): int { (y + 3) as int }
  function method Gittit(): int { (this + 2) as int }
  static method Method(y: Pos) returns (r: int) ensures r == (y + 3) as int { return (y + 3) as int; }
  method Collect() returns (r: int) ensures r == (this + 2) as int { return (this + 2) as int; }
}

// ---------- more comprehensive tests ----------

method MoreTests() {
  var d := Business(true, 5);
  var v := d.G(5);  // 10
  var u := Dt<int>.G(7);  // 14
  print d.F(10), " ", v, " ", u, "\n";  // 35 10 14
  print Dt<real>.g, " ", d.g, "\n";  // 22 22
  var yy, dd := d.M(93);
  print yy, " ", dd, "\n";  // 9 Business(false, 5)
  var a0 := d.P(54);
  var a1 := Dt<bool>.P(55);
  print a0, " ", a1, "\n";  // 76 77
  print d.c, "\n";  // 19

  var c: Co<real> := Cobalt;
  print Co<bv11>.g, " ", c.g, "\n";  // 0 0
  print c.F(2), " ", Co<bv11>.G(70), " ", c.G(71), "\n";  // 19 82 83
  var c';
  yy, c' := c.M(93);
  print yy, " ", c, "\n";  // 93 Cobalt
  a0 := c.P(54);
  a1 := Co<bool>.P(55);
  print a0, " ", a1, "\n";  // 27 27
  print c.c, "\n";  // 18

  var pr: Primes := 11;
  print pr, " ", Primes.g, " ", pr.g, " ", pr.c, "\n";  // 11 18 18 22
  print pr.F(2), " ", Primes.G(70), " ", pr.G(71), "\n";  // 15 30 29
  yy, pr := pr.M(95);
  print yy, " ", pr, "\n";  // 95 11
  a0 := pr.P(54);
  a1 := Primes.P(55);
  print a0, " ", a1, "\n";  // 162 165

  var sm: Small := 11;
  print sm, " ", Small.g, " ", sm.g, " ", sm.c, "\n";  // 11 18 18 3
  print sm.F(2), " ", Small.G(70), " ", sm.G(71), "\n";  // 15 30 29
  yy, sm := sm.M(95);
  print yy, " ", sm, "\n";  // 95 11
  a0 := sm.P(54);
  a1 := Small.P(55);
  print a0, " ", a1, "\n";  // 162 165
}

datatype Dt<A> = Blue | Bucket(diameter: real) | Business(trendy: bool, a: A)
{
  const c: int := if this.Blue? then 18 else 19
  static const g: int := 22
  function method F(x: int): int {
    x + if this.Bucket? then this.diameter.Floor else 25
  }
  static function method G(x: int): int {
    2 * x
  }
  method M(x: int) returns (y: int, d: Dt<A>) {
    if this == Blue {
      y := x;
    } else {
      y := 9;
    }
    var z := RecursiveZero(3);
    y := y + z;
    z := StaticRecursiveZero(3);
    y := y + z;
    match this
    case Blue =>
      assert y == x;
      d := Bucket(0.0);
    case Bucket(dm) =>
      d := this.(diameter := this.diameter + 2.0);
    case Business(t, a) =>
      d := this.(trendy := !t);
  }
  static method P(x: int) returns (y: int) {
    y := x + g;
  }
  twostate predicate Toop() { old(this) == this } // warning: old has no effect
  twostate lemma Tool() { }
  least predicate IndP() { true }
  greatest predicate CoP() { true }
  method RecursiveZero(x: int) returns (z: int) ensures z == 0 decreases x != 0 {
    if x == 0 { return 0; } else { z := RecursiveZero(0); }
  }
  static method StaticRecursiveZero(x: int) returns (z: int) ensures z == 0 decreases x != 0 {
    if x == 0 { return 0; } else { z := StaticRecursiveZero(0); }
  }
}
codatatype Co<A> = Cobalt | Continues(next: Co<A>)
{
  const c: int := if this.Cobalt? then 18 else 19
  static const g: int
  function method F(x: int): int { 19 }
  static function method G(x: int): int { x + 12 }
  method M(x: int) returns (y: int, d: Co<int>) {
    if this == Cobalt {
      y := x;
    } else {
      y := 9;
    }
    var z := RecursiveZero(3);
    y := y + z;
    z := StaticRecursiveZero(3);
    y := y + z;
    d := Cobalt;
  }
  static method P(x: int) returns (y: int) {
    y := x / 2;
  }
  method RecursiveZero(x: int) returns (z: int) ensures z == 0 decreases x != 0 {
    if x == 0 { return 0; } else { z := RecursiveZero(0); }
  }
  static method StaticRecursiveZero(x: int) returns (z: int) ensures z == 0 decreases x != 0 {
    if x == 0 { return 0; } else { z := StaticRecursiveZero(0); }
  }
}

newtype Primes = x | 2 <= x && forall y :: 2 <= y < x ==> x % y != 0 witness 2
{
  const c: int := this as int * 2
  static const g: int := 18
  function method F(x: int): int { 2 * x + this as int }
  static function method G(x: int): int { 100 - x }
  method M(x: int) returns (y: int, d: Primes) {
    var z := RecursiveZero(3);
    return x + z, this;
  }
  static method P(x: int) returns (y: int) {
    var z := StaticRecursiveZero(3);
    y := 3*x + z;
  }
  method RecursiveZero(x: int) returns (z: int) ensures z == 0 decreases x != 0 {
    if x == 0 { return 0; } else { z := RecursiveZero(0); }
  }
  static method StaticRecursiveZero(x: int) returns (z: int) ensures z == 0 decreases x != 0 {
    if x == 0 { return 0; } else { z := StaticRecursiveZero(0); }
  }
}

newtype Small = x | 0 <= x < 25
{
  const c := this as int % 4
  static const g: int := 18
  function method F(x: int): int { 2 * x + this as int }
  static function method G(x: int): int { 100 - x }
  method M(x: int) returns (y: int, d: Small) {
    var z := RecursiveZero(3);
    return x + z, this;
  }
  static method P(x: int) returns (y: int) {
    var z := StaticRecursiveZero(3);
    y := 3*x + z;
  }
  method RecursiveZero(x: int) returns (z: int) ensures z == 0 decreases x != 0 {
    if x == 0 { return 0; } else { z := RecursiveZero(0); }
  }
  static method StaticRecursiveZero(x: int) returns (z: int) ensures z == 0 decreases x != 0 {
    if x == 0 { return 0; } else { z := StaticRecursiveZero(0); }
  }
}

// TODO: test recursive dependencies
