/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
 Defines a low-level specification of a JSON serializer.
 */
module Std.JSON.ConcreteSyntax.Spec {
  import Vs = Utils.Views.Core
  import opened BoundedInts
  import opened Grammar

  function View(v: Vs.View) : bytes {
    v.Bytes()
  }

  function Structural<T>(self: Structural<T>, fT: T -> bytes): bytes {
    View(self.before) + fT(self.t) + View(self.after)
  }

  function StructuralView(self: Structural<Vs.View>): bytes {
    Structural<Vs.View>(self, View)
  }

  function Maybe<T>(self: Maybe<T>, fT: T -> bytes): (bs: bytes)
    ensures self.Empty? ==> bs == []
    ensures self.NonEmpty? ==> bs == fT(self.t)
  {
    if self.Empty? then [] else fT(self.t)
  }

  function ConcatBytes<T>(ts: seq<T>, fT: T --> bytes) : (b: bytes)
    requires forall d | d in ts :: fT.requires(d)
    ensures |ts| == 1 ==> b == fT(ts[0])
  {
    if |ts| == 0 then []
    else fT(ts[0]) + ConcatBytes(ts[1..], fT)
  }

  function Bracketed<D, S>(self: Bracketed<Vs.View, D, S, Vs.View>, fDatum: Suffixed<D, S> --> bytes): bytes
    requires forall d | d < self :: fDatum.requires(d)
  {
    StructuralView(self.l) +
    ConcatBytes(self.data, fDatum) +
    StructuralView(self.r)
  }

  function KeyValue(self: jKeyValue): bytes {
    String(self.k) + StructuralView(self.colon) + Value(self.v)
  }

  function Frac(self: jfrac): bytes {
    View(self.period) + View(self.num)
  }

  function Exp(self: jexp): bytes {
    View(self.e) + View(self.sign) + View(self.num)
  }

  function Number(self: jnumber): bytes {
    View(self.minus) + View(self.num) + Maybe(self.frac, Frac) + Maybe(self.exp, Exp)
  }

  function String(self: jstring): bytes {
    View(self.lq) + View(self.contents) + View(self.rq)
  }

  function CommaSuffix(c: Maybe<Structural<jcomma>>): bytes {
    // BUG(https://github.com/dafny-lang/dafny/issues/2179)
    Maybe<Structural<Vs.View>>(c, StructuralView)
  }

  function Member(self: jmember) : bytes {
    KeyValue(self.t) + CommaSuffix(self.suffix)
  }

  function Item(self: jitem) : bytes {
    Value(self.t) + CommaSuffix(self.suffix)
  }

  function Object(obj: jobject) : bytes {
    Bracketed(obj, (d: jmember) requires d < obj => Member(d))
  }

  function Array(arr: jarray) : bytes {
    Bracketed(arr, (d: jitem) requires d < arr => Item(d))
  }

  function Value(self: Value) : (b: bytes)
    ensures self.String? ==> b == String(self.str)
    ensures self.Number? ==> b == Number(self.num)
    ensures self.Object? ==> b == Object(self.obj)
    ensures self.Array? ==> b == Array(self.arr)
  {
    match self {
      case Null(n) => View(n)
      case Bool(b) => View(b)
      case String(str) => String(str)
      case Number(num) => Number(num)
      case Object(obj) => Object(obj)
      case Array(arr) => Array(arr)
    }
  }

  lemma UnfoldValueNumber(v: Value)
    requires v.Number?
    ensures Value(v) == Number(v.num)
  {
    assert Value(v) == match v { case Number(num) => Number(num) case _ => []};
  }

  lemma UnfoldValueObject(v: Value)
    requires v.Object?
    ensures Value(v) == Object(v.obj)
  {
    assert Value(v) == match v { case Object(obj) => Object(obj) case _ => []};
  }

  lemma UnfoldValueArray(v: Value)
    requires v.Array?
    ensures Value(v) == Array(v.arr)
  {
    assert Value(v) == match v { case Array(arr) => Array(arr) case _ => []};
  }

  function JSON(js: JSON) : bytes {
    Structural(js, Value)
  }
}