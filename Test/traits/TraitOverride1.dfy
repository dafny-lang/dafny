// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T1
{
  function method Plus (x:int, y:int) : int
    requires x>y
  {
    x + y
  }

  function method bb(x:int):int
    requires x>10

  function method BodyLess1(a:int) : int
    requires a > 0

  function method dd(a:int) : int

  method Testing()
}

class C1 extends T1
{
  function method dd(x:int):int
  {
    2
  }

  method Testing()
  {
    var x:int := 11;
    x := bb(x);
  }

  function method bb(x:int):int
    requires x >10
  {
    x
  }
  function method BodyLess1(bda:int) : int
    requires bda > -10
  {
    2
  }

  method CallBodyLess(x:int)
    requires x > -10
  {
    var k:int := BodyLess1(x);
    assert k==2;
  }
}

trait T2
{
  function method F(x: int): int
    requires x < 100
    ensures F(x) < 100

  method M(x: int) returns (y: int)
    requires 0 <= x
    ensures x < y
}

class C2 extends T2
{
  function method F(x: int): int
    requires x < 100
    ensures F(x) < 100
  {
    x
  }

  method M(x: int) returns (y: int)
    requires -2000 <= x  // a more permissive precondition than in the interface
    ensures 2*x < y  // a more detailed postcondition than in the interface
  {
    y := 2 * x + 1;
  }
}


trait T3
{
  function method F(y: int): int
  function method G(y: int): int { 12 }
  method M(y: int)
  method N(y: int) {
    var a:int := 100;
    assert a==100;
  }
}
class C3 extends T3
{
  function method NewFunc (a:int, b:int) : int
  {
    a + b
  }
  function method F(y: int): int { 20 }
  method M(y: int) {
    var a:int := 100;
    assert a==100;
  }
}

trait t
{
  function f(s2:int):int
    ensures f(s2) > 0
    //requires s != null && s.Length > 1
    //reads s, s2
}

class c extends t
{
  function f(s3:int):int
    ensures f(s3) > 1
    //requires s0 != null && s0.Length > (0)
    //reads s0
  {
    2
  }
}

trait TT
{
  static function method M(a:int, b:int) : int
    ensures M(a,b) == a + b
  {
    a + b
  }
}

class CC extends TT
{
  method Testing(a:int,b:int)
  {
    assert TT.M(a,b) == a + b;
  }
}


trait T4
{
  function method F(y: int): int

  function method G(y: int): int
  {
    100
  }

  method M(y: int) returns (kobra:int)
    requires y > 0
    ensures kobra > 0

  method N(y: int)
  {
    var x: int;
    var y : int;
    y := 10;
    x := 1000;
    y := y + x;
  }
}

class C4 extends T4
{
  function method F(y: int): int
  {
    200
  }

  method M(kk:int) returns (ksos:int)
    requires kk > -1
    ensures ksos > 0
  {
    ksos:=10;
  }
}

// regression tests

trait OneTrait
{
  predicate P() { true }
  predicate Q() { true }
  predicate R(x: int) { x < 80 }

  method M() ensures P()
  method N() ensures P()
  method O() returns (r: int) ensures R(r)
  method O'() returns (r: int) ensures P()
}

class OneClass extends OneTrait
{
  method M() ensures P() { }
  method N() ensures Q() { }
  method O() returns (r': int) ensures P()  // error: this postcondition does not imply the one in the trait
  {
    r' := 50;
  }
  method O'() returns (r': int) ensures R(r')
  { }  // error: does not establish postcondition R(r')
}
