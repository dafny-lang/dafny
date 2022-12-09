// RUN: %exits-with 4 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function method MkId<A>() : A -> A {
  x => x
}

function method IntId() : int ~> int {
  y => y
}

function method DivZero() : int ~> int
{
  z => 5 / z  // div by zero
}

function method DivZeroWithReq() : int ~> int
{
  (z) requires z != 0 => 5 / z
}

function method DivZero2() : (int, int) ~> int {
  (x, y) requires y != 0 => x / y
}

function method DivZero3() : int ~> int {
  z => z / 0   // div by zero
}

function method Shadow() : int ~> real ~> real {
  x => x => x
}

method Reqs() {
  var fn := (u) requires u => u;
  print fn(true);
  print fn(false);  // precond violation
}

method Main() {
  var id := IntId();
  print id(5);
  var polyid : int ~> int := MkId();
  print polyid(5);
  assert id(2) == polyid(2);
  assert id(3) != 4 && 5 != polyid(6);
  var divvy := DivZero2();
  print divvy(2,5);
  print divvy(2,0); // precond violation
}

function method succ(x : int) : int
  requires x > 0
{
  x + 1
}

method Main2() {
  var suc := succ;
  assert suc(3) == succ(3);
  assert suc(-1) == 0; // precond violation
}

function method Id<A>(x : A) : A {
  x
}


method Main3() {
  var id := Id;
  assert id(3) == 3;
  assert forall x :: (Id(id))(x) == (y => y)(x);
  assert forall x :: (Id(id))(x) == (y => y)(2); // should fail
}


function P<A,B>(f: A ~> B, x : A): B
  reads (f.reads)(x)
  requires (f.requires)(x)
{
  f(x)
}


function Q<U,V>(f: U ~> V, x : U): V
  reads P.reads(f,x)
  requires f.requires(x)  // would be nice to be able to write P.requires(f,x)
{
  P(f,x)
}

function QQ<U,V>(f: U ~> V, x : U): V
  reads ((() => ((()=>f)()).reads)())((()=>x)())
  requires ((() => ((()=>f)()).requires)())((()=>x)())
{
  ((() => P)())((()=>f)(),(()=>x)())
}

