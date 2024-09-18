/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
 Defines a high-level specification of a JSON serializer.
 */
module Std.JSON.Spec {
  import Collections.Seq
  import opened BoundedInts
  import opened Strings
  import opened Values
  import opened Wrappers
  import opened Errors
  import opened Unicode.UnicodeStringsWithUnicodeChar
  import opened Arithmetic.Logarithm

  type Result<+T> = SerializationResult<T>

  function EscapeUnicode(c: uint16): seq<uint16> {
    var sStr := Strings.HexConversion.OfNat(c as nat);
    Seq.MembershipImpliesIndexing(c => 0 <= c as int < 128, sStr);
    var s := ASCIIToUTF16(sStr);
    assert |s| <= 4 by {
      assert c as nat <= 0xFFFF;
      assert Log(16, c as nat) <= Log(16, 0xFFFF) by {
        LemmaLogIsOrdered(16, c as nat, 0xFFFF);
      }
      assert Log(16, 0xFFFF) == 3;
    }
    s + seq(4 - |s|, _ => ' ' as uint16)
  }

  function Escape(str: seq<uint16>, start: nat := 0): seq<uint16>
    decreases |str| - start
  {
    if start >= |str| then []
    else
      (match str[start]
       case 0x22 => ASCIIToUTF16("\\\"") // quotation mark
       case 0x5C => ASCIIToUTF16("\\\\") // reverse solidus
       case 0x08 => ASCIIToUTF16("\\b")  // backspace
       case 0x0C => ASCIIToUTF16("\\f")  // form feed
       case 0x0A => ASCIIToUTF16("\\n")  // line feed
       case 0x0D => ASCIIToUTF16("\\r")  // carriage return
       case 0x09 => ASCIIToUTF16("\\t")  // tab
       case c =>
         if c < 0x001F then ASCIIToUTF16("\\u") + EscapeUnicode(c)
         else [str[start]])
      + Escape(str, start + 1)
  }

  function EscapeToUTF8(str: string, start: nat := 0): Result<bytes> {
    var utf16 :- ToUTF16Checked(str).ToResult(SerializationError.InvalidUnicode);
    var escaped := Escape(utf16);
    var utf32 :- FromUTF16Checked(escaped).ToResult(SerializationError.InvalidUnicode);
    ToUTF8Checked(utf32).ToResult(SerializationError.InvalidUnicode)
  }

  // Can fail due to invalid UTF-16 sequences in a string when --unicode-char is off
  function String(str: string): Result<bytes> {
    var inBytes :- EscapeToUTF8(str);
    Success(ASCIIToUTF8("\"") + inBytes + ASCIIToUTF8("\""))
  }

  lemma OfIntOnlyASCII(n: int)
    ensures
      && var s := Strings.OfInt(n);
      && forall i | 0 <= i < |s| :: 0 <= s[i] as int < 128
  {
    var s := Strings.OfInt(n);
    forall i | 0 <= i < |s| ensures 0 <= s[i] as int < 128 {
      if i == 0 {
      } else {
        var isHexDigit := c => c in Strings.HexConversion.HEX_DIGITS;
        assert Strings.HexConversion.IsNumberStr(s, '-');
        assert isHexDigit(s[i]);
      }
    }
  }

  function IntToBytes(n: int): bytes {
    var s := Strings.OfInt(n);
    OfIntOnlyASCII(n);
    ASCIIToUTF8(s)
  }

  function Number(dec: Decimal): Result<bytes> {
    Success(IntToBytes(dec.n) +
            (if dec.e10 == 0 then []
             else ASCIIToUTF8("e") + IntToBytes(dec.e10)))
  }

  function KeyValue(kv: (string, JSON)): Result<bytes> {
    var key :- String(kv.0);
    var value :- JSON(kv.1);
    Success(key + ASCIIToUTF8(":") + value)
  }

  function Join(sep: bytes, items: seq<Result<bytes>>): Result<bytes> {
    if |items| == 0 then
      Success([])
    else
      var first :- items[0];
      if |items| == 1 then
        Success(first)
      else
        var rest :- Join(sep, items[1..]);
        Success(first + sep + rest)
  }

  function Object(obj: seq<(string, JSON)>): Result<bytes> {
    var middle :- Join(ASCIIToUTF8(","), seq(|obj|, i requires 0 <= i < |obj| => KeyValue(obj[i])));
    Success(ASCIIToUTF8("{") + middle + ASCIIToUTF8("}"))
  }

  function Array(arr: seq<JSON>): Result<bytes> {
    var middle :- Join(ASCIIToUTF8(","), seq(|arr|, i requires 0 <= i < |arr| => JSON(arr[i])));
    Success(ASCIIToUTF8("[") + middle + ASCIIToUTF8("]"))
  }

  function JSON(js: JSON): Result<bytes> {
    match js
    case Null => Success(ASCIIToUTF8("null"))
    case Bool(b) => Success(if b then ASCIIToUTF8("true") else ASCIIToUTF8("false"))
    case String(str) => String(str)
    case Number(dec) => Number(dec)
    case Object(obj) => Object(obj)
    case Array(arr) => Array(arr)
  }
}