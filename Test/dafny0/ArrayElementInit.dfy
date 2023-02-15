// RUN: %exits-with 4 %dafny /print:"%t.print" /rprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M0(d: int)
{
  var a := new int[25](_ => d);
  assert a.Length == 25;
  assert a[18] == d;
}

method M1(d: int)
{
  var a := new int[25](_ => 10 / d);  // error: possible division by 0
  assert a.Length == 25;
}

method M2(f: int ~> real)
{
  var a := new real[25](f);  // error: nothing is known about the precondition of "f"
  assert a.Length == 25;
}

method M3(f: int ~> real)
  requires forall x :: x < 25 ==> f.requires(x)
{
  var a := new real[25](f);
  assert a.Length == 25;
}

method M4(d: char)
{
  var a := new char[25](x requires 0 <= x < 25 => d);
  assert a.Length == 25;
  assert a[18] == d;
}

method M5(d: char)
{
  var a := new char[25](x requires 0 <= x < 24 => d);  // error: initialization function does not include x==24
  assert a.Length == 25;
  assert a[18] == d;
}

method P0(d: char)
{
  var a := new char[25,10,100]((_,_,_) => d);
  assert a.Length0 == 25;
  assert a.Length1 == 10;
  assert a.Length2 == 100;
  assert a[18,3,23] == d;
}

method P1(d: char)
{
  var a := new char[25,10]((x, y) => if x==y then '=' else d);
  assert a.Length0 == 25;
  assert a.Length1 == 10;
  assert a[18,3] == d;
  assert a[7,7] == '=';
}

method P2<D>(d: D, e: D)
{
  var a := new D[1,2,4,8,16]((_,_,_,_,_) => d);
  assert a.Length3 == 8;
  assert a[0,0,0,0,0] == e;  // error: no reason to think d==e
}

type Six = x | 6 <= x witness 7

method Q0(s: Six, y: int) returns (a: array<Six>)
  requires 100 <= y
{
  if
  case true =>  a := new Six[10](_ => s);
  case true =>  a := new Six[10](x => 6+x);
  case true =>  a := new Six[10](_ => y);
  case true =>  a := new Six[10];
  case true =>  a := new Six[0];
}

method Q1<D>(s: D, n: int) returns (a: array<D>)
{
  if
  case true =>  a := new D[10](_ => s);
  case true =>  a := new D[10];  // error: not allowed to allocate nonempty array of D's
  case n == 0 =>  a := new D[n];
  case 0 <= n =>  a := new D[n];  // error: not allowed to allocate nonempty array of D's
}

method QCaller()
{
  var s: Six;
  var a := Q0(s, 217);
  var b := Q1(s, 2);
}

method SubtypeConstraint(f: int ~> int, g: int ~> nat)
  requires forall x :: 0 <= x < 100 ==> f.requires(x) && g.requires(x)
{
  var a := new nat[100](g);
  var b := new nat[100](f);  // error: f may return negative numbers
}

// ------- initializing display --------------------------------------

method Display0<D>(d: D, n: int)
{
  var a := new nat[4] [100, 75, 50, 25];
  var b := new nat[4] [100, 75, n, 25];  // error: "n" may be negative
  var c := new D[2] [d, d];
  var d := new char[0][];
  var e := new real[3][2.0, 2.0, 2.0, 2.0];  // error: incorrect array size given
}

method Display1<D>(d: D, n: int, w: array<nat>)
  requires 0 <= n && 100 <= w.Length
{
  var a := new nat[4] [100, 75, 50, 25];
  assert a.Length == 4;
  assert a[0] == 100;
  assert a[1] == 75;
  assert a[2] == 50;
  assert a[3] == 25;

  var b := new nat[4] [100, 75, n, 25];
  assert b[2] == n;
  assert b[0] == b[1] + b[3];

  assert 0 <= w[23];

  var c := new D[2] [d, d];
  assert c[0] == c[1] == d;

  var d := new char[0][];
  assert d.Length == 0;

  var e := new real[2][ 100.0, 200.0 ];
  assert e[0] == e[1];  // error: no, they're not the same
}

method Display2<D>(f: int ~> D)
{
  var a := new D[1] [ f(0) ];  // error: 0 may not be in the domain of f
}

// ---------- more initialization ----------------------

method AllocateMatrix<D>(a: nat, b: nat, c: nat) returns (o: object)
{
  if
  case true =>  o := new D[a];  // error: might request nonempty array
  case a == 0 =>  o := new D[a];
  case true =>  o := new D[a,b];  // error: might request nonempty array
  case a == 0 =>  o := new D[a,b];
  case b == 0 =>  o := new D[a,b];
  case a+b == 0 =>  o := new D[a,b];
  case true =>  o := new D[a,b,c];  // error: might request nonempty array
  case a == 0 =>  o := new D[a,b,c];
  case b == 0 =>  o := new D[a,b,c];
  case c == 0 =>  o := new D[a,b,c];
  case a+b == 0 || b+c == 0 || c+a == 0 =>  o := new D[a,b,c];
}
