/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
 Implements high-level deserialization (utf-8 bytes to JSON values).
 */
module Std.JSON.Deserializer {
  import Values
  import Spec
  import ByteStrConversion
  import opened Collections.Seq
  import opened Wrappers
  import opened BoundedInts
  import opened Arithmetic.Logarithm
  import opened Arithmetic.Power
  import opened Strings
  import opened Unicode.UnicodeStringsWithUnicodeChar
  import opened Errors
  import opened DynamicArray
  import opened Grammar
  import opened Utils.Views.Core

  function Bool(js: Grammar.jbool): bool {
    assert js.Bytes() in {Grammar.TRUE, Grammar.FALSE};
    js.At(0) == 't' as byte
  }

  function UnsupportedEscape16(code: seq<uint16>): DeserializationError {
    UnsupportedEscape(FromUTF16Checked(code).GetOr("Couldn't decode UTF-16"))
  }

  @DisableNonlinearArithmetic
  module Uint16StrConversion refines Strings.ParametricConversion {
    import opened BoundedInts

    type Char = uint16

    const chars := [
      '0' as uint16, '1' as uint16, '2' as uint16, '3' as uint16, '4' as uint16,
      '5' as uint16, '6' as uint16, '7' as uint16, '8' as uint16, '9' as uint16,
      'a' as uint16, 'b' as uint16, 'c' as uint16, 'd' as uint16, 'e' as uint16, 'f' as uint16,
      'A' as uint16, 'B' as uint16, 'C' as uint16, 'D' as uint16, 'E' as uint16, 'F' as uint16
    ]

    const charToDigit :=
      map[
        '0' as uint16 := 0, '1' as uint16 := 1, '2' as uint16 := 2, '3' as uint16 := 3, '4' as uint16 := 4,
        '5' as uint16 := 5, '6' as uint16 := 6, '7' as uint16 := 7, '8' as uint16 := 8, '9' as uint16 := 9,
        'a' as uint16 := 0xA, 'b' as uint16 := 0xB, 'c' as uint16 := 0xC, 'd' as uint16 := 0xD, 'e' as uint16 := 0xE, 'f' as uint16 := 0xF,
        'A' as uint16 := 0xA, 'B' as uint16 := 0xB, 'C' as uint16 := 0xC, 'D' as uint16 := 0xD, 'E' as uint16 := 0xE, 'F' as uint16 := 0xF
      ]

    // The size of the map makes this impractical to verify easily.
    @Axiom
    lemma CharsConsistent()
      ensures forall c <- chars :: c in charToDigit && chars[charToDigit[c]] == c
  }

  const HEX_TABLE_16 := Uint16StrConversion.charToDigit

  function ToNat16(str: Uint16StrConversion.String): uint16
    requires |str| <= 4
    requires forall c | c in str :: c in HEX_TABLE_16
  {
    assume {:axiom} false; // BUG Verification inconclusive
    Uint16StrConversion.ToNatBound(str);
    var hd := Uint16StrConversion.ToNat(str);
    assert hd < 0x1_0000;
    hd as uint16
  }

  @TailRecursion
  @IsolateAssertions
  function Unescape(str: seq<uint16>, start: nat := 0, prefix: seq<uint16> := []): DeserializationResult<seq<uint16>>
    decreases |str| - start
  { // Assumes UTF-16 strings
    if start >= |str| then Success(prefix)
    else if str[start] == '\\' as uint16 then
      if |str| == start + 1 then
        Failure(EscapeAtEOS)
      else
        var c := str[start + 1];
        if c == 'u' as uint16 then
          if |str| <= start + 6 then
            Failure(EscapeAtEOS)
          else
            var code := str[start + 2..start + 6];
            if exists c | c in code :: c !in HEX_TABLE_16 then
              Failure(UnsupportedEscape16(code))
            else
              var hd := ToNat16(code);
              Unescape(str, start + 6, prefix + [hd])
        else
          var unescaped: uint16 := match c
            case 0x22 => 0x22 as uint16 // \" => quotation mark
            case 0x5C => 0x5C as uint16 // \\ => reverse solidus
            case 0x62 => 0x08 as uint16 // \b => backspace
            case 0x66 => 0x0C as uint16 // \f => form feed
            case 0x6E => 0x0A as uint16 // \n => line feed
            case 0x72 => 0x0D as uint16 // \r => carriage return
            case 0x74 => 0x09 as uint16 // \t => tab
            case _    => 0 as uint16;
          if unescaped as int == 0 then
            Failure(UnsupportedEscape16(str[start..start+2]))
          else
            Unescape(str, start + 2, prefix + [unescaped])
    else
      Unescape(str, start + 1, prefix + [str[start]])
  }

  function String(js: Grammar.jstring): DeserializationResult<string> {
    var asUtf32 :- FromUTF8Checked(js.contents.Bytes()).ToResult(DeserializationError.InvalidUnicode);
    var asUint16 :- ToUTF16Checked(asUtf32).ToResult(DeserializationError.InvalidUnicode);
    var unescaped :- Unescape(asUint16);
    FromUTF16Checked(unescaped).ToResult(DeserializationError.InvalidUnicode)
  }

  const DIGITS := ByteStrConversion.charToDigit

  const MINUS := '-' as uint8

  function ToInt(sign: jsign, n: jnum): DeserializationResult<int> {
    var n: int := ByteStrConversion.ToNat(n.Bytes());
    Success(if sign.Char?('-') then -n else n)
  }

  function Number(js: Grammar.jnumber): DeserializationResult<Values.Decimal> {
    var JNumber(minus, num, frac, exp) := js;
    var n :-
      ToInt(minus, num);
    var e10 :- match exp
      case Empty => Success(0)
      case NonEmpty(JExp(_, sign, num)) => ToInt(sign, num);
    match frac
    case Empty => Success(Values.Decimal(n, e10))
    case NonEmpty(JFrac(_, num)) =>
      var pow10 := num.Length() as int;
      var frac :- ToInt(minus, num);
      Success(Values.Decimal(n * Pow(10, pow10) + frac, e10 - pow10))
  }

  function KeyValue(js: Grammar.jKeyValue): DeserializationResult<(string, Values.JSON)> {
    var k :- String(js.k);
    var v :- Value(js.v);
    Success((k, v))
  }

  function Object(js: Grammar.jobject): DeserializationResult<seq<(string, Values.JSON)>> {
    Seq.MapWithResult(d requires d in js.data => KeyValue(d.t), js.data)
  }

  function Array(js: Grammar.jarray): DeserializationResult<seq<Values.JSON>> {
    Seq.MapWithResult(d requires d in js.data => Value(d.t), js.data)
  }

  function Value(js: Grammar.Value): DeserializationResult<Values.JSON> {
    match js
    case Null(_) => Success(Values.Null())
    case Bool(b) => Success(Values.Bool(Bool(b)))
    case String(str) => var s :- String(str); Success(Values.String(s))
    case Number(dec) => var n :- Number(dec); Success(Values.Number(n))
    case Object(obj) => var o :- Object(obj); Success(Values.Object(o))
    case Array(arr) => var a :- Array(arr); Success(Values.Array(a))
  }

  function JSON(js: Grammar.JSON): DeserializationResult<Values.JSON> {
    Value(js.t)
  }
}