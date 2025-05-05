/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/**
  * A concrete implementation of `AbstractUnicodeStrings` for `--unicode-char:true`,
  * defining functions for converting between strings and UTF-8/UTF-16.
  * See the `AbstractUnicodeStrings` module for details.
  */
module Std.Unicode.UnicodeStringsWithUnicodeChar refines AbstractUnicodeStrings {

  import Base
  import Utf8EncodingForm
  import Utf16EncodingForm

  @IsolateAssertions
  lemma CharIsUnicodeScalarValue(c: char)
    ensures
      && var asBits := c as int as bv24;
      && asBits <= 0x10_FFFF
      && (0 <= asBits < Base.HIGH_SURROGATE_MIN || Base.LOW_SURROGATE_MAX < asBits)
  {
    assert c as int < 0x11_0000;
    // This seems to be just too expensive to verify for such a wide bit-vector type,
    // but is clearly true given the above.
    assume {:axiom} c as int as bv24 < 0x11_0000 as bv24;
    var asBits := c as int as bv24;
    assert asBits < 0x11_0000 as bv24;
    assert (asBits < Base.HIGH_SURROGATE_MIN || asBits > Base.LOW_SURROGATE_MAX);
    assert asBits <= 0x10_FFFF;
  }

  lemma UnicodeScalarValueIsChar(sv: Base.ScalarValue)
    ensures
      && var asInt := sv as int;
      && (0 <= asInt < 0xD800 || 0xE000 <= asInt < 0x11_0000)
  {
    var asInt := sv as int;
    assert (asInt < 0xD800 || asInt > 0xDFFF);
    assert (asInt < 0xDBFF || asInt > 0xDC00);
  }

  function CharAsUnicodeScalarValue(c: char): Base.ScalarValue {
    CharIsUnicodeScalarValue(c);
    c as int as Base.ScalarValue
  }

  function CharFromUnicodeScalarValue(sv: Base.ScalarValue): char {
    UnicodeScalarValueIsChar(sv);
    // TODO: Can we avoid the extra cast to int?
    sv as int as char
  }

  function ToUTF8Checked(s: string): Option<seq<uint8>>
    ensures ToUTF8Checked(s).Some?
  {
    var asCodeUnits := Seq.Map(CharAsUnicodeScalarValue, s);
    var asUtf8CodeUnits := Utf8EncodingForm.EncodeScalarSequence(asCodeUnits);
    var asBytes := Seq.Map(cu => cu as uint8, asUtf8CodeUnits);
    Some(asBytes)
  }

  function FromUTF8Checked(bs: seq<uint8>): Result<string, string> {
    var asCodeUnits := Seq.Map(c => c as Utf8EncodingForm.CodeUnit, bs);
    var utf32 :- Utf8EncodingForm.DecodeCodeUnitSequenceChecked(asCodeUnits);
    var asChars := Seq.Map(CharFromUnicodeScalarValue, utf32);
    Success(asChars)
  }

  function ToUTF16Checked(s: string): Option<seq<uint16>>
    ensures ToUTF16Checked(s).Some?
  {
    var asCodeUnits := Seq.Map(CharAsUnicodeScalarValue, s);
    var asUtf16CodeUnits := Utf16EncodingForm.EncodeScalarSequence(asCodeUnits);
    var asBytes := Seq.Map(cu => cu as uint16, asUtf16CodeUnits);
    Some(asBytes)
  }

  function FromUTF16Checked(bs: seq<uint16>): Result<string, string> {
    var asCodeUnits := Seq.Map(c => c as Utf16EncodingForm.CodeUnit, bs);
    var utf32 :- Utf16EncodingForm.DecodeCodeUnitSequenceChecked(asCodeUnits);
    var asChars := Seq.Map(CharFromUnicodeScalarValue, utf32);
    Success(asChars)
  }
}
