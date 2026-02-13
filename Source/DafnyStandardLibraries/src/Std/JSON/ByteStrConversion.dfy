/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
 Derives conversions to and from sequences of bytes.
 */
@DisableNonlinearArithmetic
module Std.JSON.ByteStrConversion refines Strings.ParametricConversion {
  import opened BoundedInts

  type Char = byte

  const chars := [
    '0' as byte, '1' as byte, '2' as byte, '3' as byte,
    '4' as byte, '5' as byte, '6' as byte, '7' as byte,
    '8' as byte, '9' as byte
  ]

  const charToDigit := map[
                         '0' as byte := 0, '1' as byte := 1, '2' as byte := 2, '3' as byte := 3,
                         '4' as byte := 4, '5' as byte := 5, '6' as byte := 6, '7' as byte := 7,
                         '8' as byte := 8, '9' as byte := 9
                       ]

  lemma CharsConsistent()
    ensures forall c <- chars :: c in charToDigit && chars[charToDigit[c]] == c
  {}
}