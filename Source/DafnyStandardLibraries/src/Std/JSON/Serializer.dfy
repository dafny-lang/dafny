/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
 Implements high-level serialization (JSON values to utf-8 bytes).
 */
module Std.JSON.Serializer {
  import Collections.Seq
  import Math
  import Values
  import Spec
  import opened Wrappers
  import opened BoundedInts
  import opened Strings
  import opened Errors
  import opened DynamicArray
  import opened Grammar
  import opened Utils.Views.Core
  import ByteStrConversion

  type Result<+T> = SerializationResult<T>
  type bytes = seq<uint8>
  type bytes32 = bs: bytes | |bs| < TWO_TO_THE_32
  type string32 = s: string | |s| < TWO_TO_THE_32

  function Bool(b: bool): jbool {
    View.OfBytes(if b then TRUE else FALSE)
  }

  function CheckLength<T>(s: seq<T>, err: SerializationError): Outcome<SerializationError> {
    Outcome.Need(|s| < TWO_TO_THE_32, err)
  }

  function String(str: string): Result<jstring> {
    var bs :- Spec.EscapeToUTF8(str);
    var o := CheckLength(bs, StringTooLong(str));
    if o.Pass? then
      Success(Grammar.JString(Grammar.DOUBLEQUOTE, View.OfBytes(bs), Grammar.DOUBLEQUOTE))
    else
      Failure(o.error)
  }

  function Sign(n: int): jminus {
    View.OfBytes(if n < 0 then ['-' as byte] else [])
  }

  const DIGITS := ByteStrConversion.chars
  const MINUS := '-' as byte

  function Int'(n: int): (str: bytes)
    ensures forall c | c in str :: c in DIGITS || c == MINUS
  {
    ByteStrConversion.OfInt(n, MINUS)
  }

  function Int(n: int): Result<View> {
    var bs := Int'(n);
    var o := CheckLength(bs, IntTooLarge(n));
    if o.Pass? then
      Success(View.OfBytes(bs))
    else
      Failure(o.error)
  }

  @IsolateAssertions
  @ResourceLimit("1e6")
  function Number(dec: Values.Decimal): Result<jnumber> {
    var minus: jminus := Sign(dec.n);
    var num: jnum :- Int(Math.Abs(dec.n));
    var frac: Maybe<jfrac> := Empty();
    var exp: Maybe<jexp> :-
      if dec.e10 == 0 then
        Success(Empty())
      else
        var e: je := View.OfBytes(['e' as byte]);
        var sign: jsign := Sign(dec.e10);
        var num: jnum :- Int(Math.Abs(dec.e10));
        Success(NonEmpty(JExp(e, sign, num)));
    Success(JNumber(minus, num, Empty, exp))
  }

  function MkStructural<T>(v: T): Structural<T> {
    Structural(EMPTY, v, EMPTY)
  }

  const COLON: Structural<jcolon> :=
    MkStructural(Grammar.COLON)

  function KeyValue(kv: (string, Values.JSON)): Result<jKeyValue> {
    var k :- String(kv.0);
    var v :- Value(kv.1);
    Success(Grammar.KeyValue(k, COLON, v))
  }

  function MkSuffixedSequence<D, S>(ds: seq<D>, suffix: Structural<S>, start: nat := 0)
    : SuffixedSequence<D, S>
    decreases |ds| - start
  {
    if start >= |ds| then []
    else if start == |ds| - 1 then [Suffixed(ds[start], Empty)]
    else [Suffixed(ds[start], NonEmpty(suffix))] + MkSuffixedSequence(ds, suffix, start + 1)
  }

  const COMMA: Structural<jcomma> :=
    MkStructural(Grammar.COMMA)

  function Object(obj: seq<(string, Values.JSON)>): Result<jobject> {
    var items :- Seq.MapWithResult(v requires v in obj => KeyValue(v), obj);
    Success(Bracketed(MkStructural(LBRACE),
                      MkSuffixedSequence(items, COMMA),
                      MkStructural(RBRACE)))
  }


  function Array(arr: seq<Values.JSON>): Result<jarray> {
    var items :- Seq.MapWithResult(v requires v in arr => Value(v), arr);
    Success(Bracketed(MkStructural(LBRACKET),
                      MkSuffixedSequence(items, COMMA),
                      MkStructural(RBRACKET)))
  }

  function Value(js: Values.JSON): Result<Grammar.Value> {
    match js
    case Null => Success(Grammar.Null(View.OfBytes(NULL)))
    case Bool(b) => Success(Grammar.Bool(Bool(b)))
    case String(str) => var s :- String(str); Success(Grammar.String(s))
    case Number(dec) => var n :- Number(dec); Success(Grammar.Number(n))
    case Object(obj) => var o :- Object(obj); Success(Grammar.Object(o))
    case Array(arr) => var a :- Array(arr); Success(Grammar.Array(a))
  }

  function JSON(js: Values.JSON): Result<Grammar.JSON> {
    var val :- Value(js);
    Success(MkStructural(val))
  }
}
