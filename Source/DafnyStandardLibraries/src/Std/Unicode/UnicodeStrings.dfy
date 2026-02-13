/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/**
  * This abstract module is an interface for converting
  * between the Dafny `string` type and sequences of UTF-8 and UTF-16
  * codepoints, where codepoints are represents as bounded ints
  * (`uint8` and `uint16`).
  *
  * Because the `--unicode-char` option changes the meaning
  * of the `char` type and hence the `string` type,
  * this module must be implemented differently for each option value.
  * Currently, the only available implementation is for `--unicode-char:true`,
  * and the implementation for `--unicode-char false` is upcoming.
  *
  * If you also want to maintain code that works for either `--unicode-char` value,
  * implement your logic in an abstract module that imports this one.
  * Then define a refining module for each `--unicode-char` value you wish to support,
  * each of which imports the appropriate implementation of AbstractUnicodeStrings.
  */
abstract module Std.Unicode.AbstractUnicodeStrings {

  import Collections.Seq

  import opened Wrappers
  import opened BoundedInts

  function ToUTF8Checked(s: string): Option<seq<uint8>>

  function ASCIIToUTF8(s: string): seq<uint8>
    requires forall i | 0 <= i < |s| :: 0 <= s[i] as int < 128
  {
    Seq.Map(c requires 0 <= c as int < 128 => c as uint8, s)
  }

  function FromUTF8Checked(bs: seq<uint8>): Result<string, string>

  function ToUTF16Checked(s: string): Option<seq<uint16>>

  function ASCIIToUTF16(s: string): seq<uint16>
    requires forall i | 0 <= i < |s| :: 0 <= s[i] as int < 128
  {
    Seq.Map(c requires 0 <= c as int < 128 => c as uint16, s)
  }

  function FromUTF16Checked(bs: seq<uint16>): Result<string, string>
}
