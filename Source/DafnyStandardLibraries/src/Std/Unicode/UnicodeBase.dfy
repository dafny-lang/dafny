/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/**
  * This module implements basic functionality of Unicode 15.1.0.
  */
module Std.Unicode.Base {
  /**
    * Any value in the Unicode codespace (a range of integers from 0 to 10FFFF_16). (Section 3.4 D9-D10)
    */
  type CodePoint = i: bv24 | 0 <= i <= 0x10FFFF

  /**
    * A Unicode code point in the range U+D800 to U+DBFF. (Section 3.8 D71)
    */
  type HighSurrogateCodePoint = p: CodePoint | HIGH_SURROGATE_MIN <= p <= HIGH_SURROGATE_MAX
    witness HIGH_SURROGATE_MIN
  const HIGH_SURROGATE_MIN: CodePoint := 0xD800
  const HIGH_SURROGATE_MAX: CodePoint := 0xDBFF

  /**
    * A Unicode code point in the range U+DC00 to U+DFFF. (Section 3.8 D73)
    */
  type LowSurrogateCodePoint = p: CodePoint | LOW_SURROGATE_MIN <= p <= LOW_SURROGATE_MAX
    witness LOW_SURROGATE_MIN
  const LOW_SURROGATE_MIN: CodePoint := 0xDC00
  const LOW_SURROGATE_MAX: CodePoint := 0xDFFF

  /**
    * Any Unicode code point except high-surrogate and low-surrogate code points. (Section 3.9 D76)
    */
  type ScalarValue = p: CodePoint |
      && (p < HIGH_SURROGATE_MIN || p > HIGH_SURROGATE_MAX)
      && (p < LOW_SURROGATE_MIN || p > LOW_SURROGATE_MAX)

  const ASSIGNED_PLANES: set<bv8> := {
    0,  // Basic Multilingual Plane
    1,  // Supplementary Multilingual Plane
    2,  // Supplementary Ideographic Plane
    3,  // Tertiary Ideographic Plane
    14, // Supplementary Special Purpose Plane
    15, // Supplementary Private Use Area A
    16  // Supplementary Private Use Area B
  }

  predicate IsInAssignedPlane(i: CodePoint) {
    var plane := (i >> 16) as bv8;
    plane in ASSIGNED_PLANES
  }

  // These are actually supersets of the Unicode planes,
  // since not all code points in a plane are assigned.
  //
  // TODO: check against the list of assigned code points, instead of only checking their plane
  // (https://www.unicode.org/Public/UCD/latest/ucd/UnicodeData.txt)
  type AssignedCodePoint = p: CodePoint | IsInAssignedPlane(p) witness *
}
