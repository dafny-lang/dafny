// RUN: %exits-with 4 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Dt = Make(d: int)

function GetNat(dt: Dt): nat {
  match dt
  // regression: the following declaration of y was once missing the subet-constraint check
  case Make(y: nat) => y  // error: dt.d is not a nat
}

method GetNatMethod(dt: Dt) returns (n: nat) {
  match dt
  // regression: the following declaration of w was once missing the subet-constraint check
  case Make(w: nat) =>  // error: dt.d is not a nat
    n := w;
}

function Works(dt: Dt): nat {
  dt.d  // error: dt.d is not a nat
}

method Main() {
  var dt := Make(-5);
  var d := GetNat(dt);
  assert 0 <= d;
  assert d == -5;
  assert false;
  print d, "\n";
}

datatype Gen<X> = Create(x: X)

method GetXX<X>(g: Gen) returns (m: X) {
  assert true;  // just to show a proof obligation in the Boogie program
  match g
  case Create(ux: X) => m := ux;
}
method GetXNat(g: Gen<nat>) returns (m: nat) {
  assert true;  // just to show a proof obligation in the Boogie program
  match g
  case Create(un: nat) => m := un;
}
method GetXInt(g: Gen<int>) returns (m: nat) {
  match g
  // regression: the following declaration of un was once missing the subet-constraint check
  case Create(un: nat) =>  // error: g.x is an int, not a nat
    m := un;
}

newtype IntA = int
type IntB = k: IntA | k % 2 == 0
type IntC = k: IntB | 0 <= k

method B2C(g: Gen<IntB>, m: IntA) returns (y: IntC)
  requires m < 0 ==> m % 2 == 1  // negative numbers are odd
{
  if g.x == m {
    match g
    case Create(u: IntC) =>  // a proof obligation is generated for this line: that (u:IntB) implies (c:IntC) here
      y := u;
  }
}

type GenSub<Y, L(00), V> = g: Gen<L> | true ghost witness Create(var l: L :| true; l)

method B2C'(g: GenSub<bool, IntB, real>, m: IntA) returns (y: IntC)
  requires m < 0 ==> m % 2 == 1  // negative numbers are odd
{
  if g.x == m {
    match g
    case Create(u: IntC) =>  // a proof obligation is generated for this line: that (u:IntB) implies (c:IntC) here
      y := u;
  }
}
