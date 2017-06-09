// RUN: %dafny /print:"%t.print" /rprint:"%t.dprint" "%s" > "%t"
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

method M2(f: int -> real)
{
  var a := new real[25](f);  // error: nothing is known about the precondition of "f"
  assert a.Length == 25;
}

method M3(f: int -> real)
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
  //TODO:  case true =>  a := new D[10];  // error: not allowed to allocate nonempty array of D's
  case n == 0 =>  a := new D[n];
  //TODO:  case 0 <= n =>  a := new D[n];  // error: not allowed to allocate nonempty array of D's
}

method QCaller()
{
  var s: Six;
  var a := Q0(s, 217);
  var b := Q1(s, 2);
}
