// RUN: %exits-with 4 %dafny /compile:0 /typeSystemRefresh:1 /print:"%t.print" /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Str(s: string) {
  var t := s;
}

class Class<XX> {
}

method MC(c: Class<real>) {
  var d: Class := c;
}

type Synonym<A, Unused> = seq<A>

method SM(x: Synonym<int, real>, y: seq<bool>) {
  var m: seq := y;

  var a := x;

  var b: Synonym := x;
  
  var k: seq := x;
  var y: Synonym := k;
}

type ParamSub<X> = s | s == CC.GetEmpty<X>()

class CC {
  static function GetEmpty<Y>(): seq<Y> {
    []
  }
}

method Q0() returns (b: array<ParamSub<real>>, be: ParamSub<real>)
{
  if * {
    // The following gives a verification error, because the inferred RHS type is the pre-type array<seq<real>>.
    // (Once type improvement for subset types is implemented, this error will go away.)
    b := new ParamSub<real>[20];
  } else {
    // The following gives a verification error, because the inferred RHS type is the pre-type array<seq<real>>.
    // (Once type improvement for subset types is implemented, this error will go away.)
    b := new ParamSub[20];
  }
  var a := be;
  var d: array := b;
  var c: ParamSub := b[0];

  b := new [20];
  var arr := new array<seq<int>>;
  var cc := new CC;
}

type K0 = y | y == C.F(2) witness *
type L0 = y | y == C.G(2) witness *
type M0 = y | y == C.H(2) witness *

class C {
  static function F(x: nat): nat {
    var u := x; u
  }
  static function G<X>(x: X): X {
    var u := x; u
  }
  static function H<X>(x: X): seq<X> {
    var u := [x]; u
  }
  static function Poly<X>(): seq<X> {
    []
  }
}

type K = y | y == C.F(2) witness *
type L = y | y == C.G(2) witness *
type M = y | y == C.H(2) witness *

type MX<X> = y | y == C.Poly<X>() witness *

class PolyClass<Z> {
  static function StaticPoly<Z>(): seq<Z> {
    var zs: seq<Z> := [];
    zs
  }
  function InstancePoly<Z>(): seq<Z> {
    var zs: seq<Z> := [];
    zs
  }
  function InstanceMono(): seq<Z> {
    var zs: seq<Z> := [];
    zs
  }
}

function FF<Y>(): K


method Q1() {
  var b: array<Six>;
}

method MM(n: nat, x: int)
{
  var r := n + x;
}

type Opaque

type Six = x | 0 <= x witness 7

type XParamSub<X> = s | s == XGetEmpty<X>()

function XGetEmpty<Y>(): seq<Y> {
  []
}

newtype N = x | x == n witness 2
const n: int := 2

const n' := 2
