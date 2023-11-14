/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/
/**
XXX
*/
abstract module {:options "-functionSyntax:4"} DafnyStdLibs.Unicode.AbstractUnicodeStrings {
  import Collections.Seq
  import opened Wrappers
  import opened BoundedInts

  function ToUTF8Checked(s: string): Option<seq<uint8>>

  function ASCIIToUTF8(s: string): seq<uint8>
    requires forall i | 0 <= i < |s| :: 0 <= s[i] as int < 128
  {
    Seq.Map(c requires 0 <= c as int < 128 => c as uint8, s)
  }

  function FromUTF8Checked(bs: seq<uint8>): Option<string>

  function ToUTF16Checked(s: string): Option<seq<uint16>>

  function ASCIIToUTF16(s: string): seq<uint16>
    requires forall i | 0 <= i < |s| :: 0 <= s[i] as int < 128
  {
    Seq.Map(c requires 0 <= c as int < 128 => c as uint16, s)
  }

  function FromUTF16Checked(bs: seq<uint16>): Option<string>
}