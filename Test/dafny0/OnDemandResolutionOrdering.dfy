// RUN: %dafny /compile:0 /typeSystemRefresh:1 /print:"%t.print" /rprint:"%t.rprint" "%s" > "%t"
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

  var b: Synonym<int, bool> := x; // fine

  var k: seq := x;
  var y: Synonym<int, bv29> := k; // fine
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
    b := new ParamSub<real>[20];
  } else {
    b := new ParamSub[20];
  }
  var a := be;
  var d: array := b;
  var c: ParamSub := b[0];

  // For the type in the following RHS, note that type adjustments (currently) flow only from RHSs to LHSs, so it would
  // not adjust "seq<real>" to "ParamSub<real>". However, the .PrintablePreType of the pre-type is recorded (from the declaration
  // of parameter "b"), so pre-type inference retains that information. Consequently, the RHS type is inferred as
  // "ParamSub<real>", so the assignment works out.
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

module VariationOnOrdering0 {
  type ParamSub<X> = s | s == CC.GetEmpty<X>()

  class CC {
    static function GetEmpty<Y>(): seq<Y> {
      []
    }
  }

  class QQ {
    // In this module, Q0 follows ParamSub and GetEmpty
    method Q0() returns (b: array<ParamSub<real>>)
    {
      b := new ParamSub<real>[20];
    }
  }
}

module VariationOnOrdering1 {
  class QQ {
    // In this module, Q0 precedes ParamSub and GetEmpty
    method Q0() returns (b: array<ParamSub<real>>)
    {
      b := new ParamSub<real>[20];
    }
  }

  type ParamSub<X> = s | s == CC.GetEmpty<X>()

  class CC {
    static function GetEmpty<Y>(): seq<Y> {
      []
    }
  }
}

module Ordering0 {
  class C {
    // The use of Dt.Make in the next line causes the pre-type of Dt.Make to be computed. This test
    // makes sure that the pre-type of Dt.Make is not called again while visiting the declaration of Dt.
    const Y := Make(10)
  }

  datatype Dt = Make(i: int)
}

module Ordering1 {
  // The use of Func in the next line causes the pre-types of the signature of Func to be computed. This test
  // makes sure that the pre-types of Func are not called again while visiting the declaration of Func.
  const Y := Func(10)

  function Func(i: int): real
}

module Ordering2 {
  class C {
    // The use of Dt.Make in the next line causes the pre-type of Dt.Make to be computed. This test
    // makes sure that the pre-type of Dt.Make is not called again while visiting the declaration of Dt.
    const Y := D.Func(10)
  }

  class D {
    static function Func(i: int): real
  }
}

module Ordering3 {
  class C {
    // The use of D.Lemma in the next line causes the pre-types of the signature of Lemma to be computed. This test
    // makes sure that the pre-types of Lemma are not called again while visiting the declaration of Lemma.
    const Y := (D.Lemma(10); 27)
  }

  class D {
    static lemma Lemma(i: int)
  }
}
