// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var next: C
  var x: int
}

function F(c: C): int
  reads c
{
  c.x
}

twostate function G(a: C, new b: C): int
  reads b
{
  old(a.x) + b.x
}

lemma L(c: C)
{ }

twostate lemma K(a: C, new B: C)
{ }

method M0(p: C)
{
  var c, d := new C, new C;
  ghost var x;
  if
  case true =>
    x := F(c);
  case true =>
    x := old(F(c));  // error
  case true =>
    x := old(L(  // BUG: should check L's parameter to be allocated in the old state
               if F(d) == 10 then c else c  // error
             ); 5);
  case true =>
    x := old(L(  // BUG: should check L's parameter to be allocated in the old state
               if F(p) == 10 then c else c
             ); 5);
  case true =>
    x := old(L(c); 5);  // BUG: should check L's parameter to be allocated in the old state
  }
method M1(p: C)
{
  var c := new C;
  ghost var x;
  if
  case true =>
    x := old(assert F(c) == 5; 5);  // error
  case true =>
    x := old(calc {
               5;
               { L(c); }  // BUG: should check L's parameter to be allocated in the old state
               5;
               F(c);  // error
             }
             10);
}
method M2(p: C)
{
  var c := new C;
  ghost var x;
  if
  case true =>
    x := (K(c, c); 5);  // error
  case true =>
    x := (K(p, c); 5);
  case true =>
    x := c.x;
  case true =>
    x := old(c.x);  // error
  case true =>
    x := G(p, c);
  case true =>
    x := G(c, c);  // error
}
