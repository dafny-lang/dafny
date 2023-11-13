/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/**
 * A concrete implementation of `AbstractUnicodeStrings` for `--unicode-char:false`,
 * defining functions for converting between strings and UTF-8/UTF-16.
 * See the `AbstractUnicodeStrings` module for details.
 */
module DafnyStdLibs.Unicode.UnicodeStringsWithoutUnicodeChar refines AbstractUnicodeStrings {

  import Base
  import Utf8EncodingForm
  import Utf16EncodingForm

  predicate IsWellFormedString(s: string)
    ensures |s| == 0 ==> IsWellFormedString(s)
  {
    Utf16EncodingForm.IsWellFormedCodeUnitSequence(Seq.Map(c => c as Utf16EncodingForm.CodeUnit, s))
  }

  function ToUTF8Checked(s: string): Option<seq<uint8>> {
    var asCodeUnits := Seq.Map(c => c as Utf16EncodingForm.CodeUnit, s);
    var utf32 :- Utf16EncodingForm.DecodeCodeUnitSequenceChecked(asCodeUnits);
    var asUtf8CodeUnits := Utf8EncodingForm.EncodeScalarSequence(utf32);
    Some(Seq.Map(c => c as uint8, asUtf8CodeUnits))
  }

  function {:vcs_split_on_every_assert} FromUTF8Checked(bs: seq<uint8>): Option<string> {
    var asCodeUnits := Seq.Map(c => c as Utf8EncodingForm.CodeUnit, bs);
    var utf32 :- Utf8EncodingForm.DecodeCodeUnitSequenceChecked(asCodeUnits);
    var asUtf16CodeUnits := Utf16EncodingForm.EncodeScalarSequence(utf32);
    Some(Seq.Map(cu => cu as char, asUtf16CodeUnits))
  }

  function ToUTF16Checked(s: string): Option<seq<uint16>> {
    if Utf16EncodingForm.IsWellFormedCodeUnitSequence(Seq.Map(c => c as Utf16EncodingForm.CodeUnit, s)) then
      Some(Seq.Map(c => c as uint16, s))
    else
      None
  }

  function FromUTF16Checked(bs: seq<uint16>): Option<string> {
    if Utf16EncodingForm.IsWellFormedCodeUnitSequence(Seq.Map(c => c as Utf16EncodingForm.CodeUnit, bs)) then
      Some(Seq.Map(c => c as char, bs))
    else
      None
  }
}
