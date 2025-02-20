// RUN: %exits-with 4 %verify --show-hints "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Main {
  newtype b1 = x | 0 <= x < 3/(2-2)
  newtype b2 = x | 0 <= x < 3%(2-2)
  newtype b3 = x | 0 <= x < (3.0/(2.0-2.0)) as int
  newtype b4 = x | 0 <= x < 1.5 as int
  newtype b5 = x | 0 <= x < 1000.0 as int as bv8 as int
  newtype b6 = x | 0 <= x < 100.5 as int as bv8 as int
  newtype b8 = x | 0 <= x < 1000 as bv8 as int
  newtype b9 = x | 0 <= x < 1000 as bv16 as bv8 as int
  newtype b10 = x | 0 <= x < -1 as int as char as int
  newtype b11 = x | 0 <= x < -1 as real as int as char as int
  newtype b12 = x | 0 <= x < 1.5 as real as int as char as int
  newtype b13 = x | 0 <= x < 'c' as int as bv2 as int
  newtype b14 = x | 0 <= x < 0xffffff as bv32 as int as char as int
  newtype b15 = x | 0 <= x < ((10 as bv8)/(0 as bv8)) as int
  newtype b16 = x | 0 <= x < ((10 as bv8)%(0 as bv8)) as int
  newtype b17 = x | 0 <= x < (10 as bv8 << -1) as int
  newtype b18 = x | 0 <= x < (10 as bv8 >> -1) as int

  newtype c0 = x | 0 <= x < 100
  class Default {
    static const cc1: c0 := 50
  }
  newtype c1 = x | 0 <= x < 50 as c0 // not constant-folded
  newtype c2 = x: int | 0 <= x < Default.cc1 as int // evaluated

  newtype c3 = x | 0 <= x < "abcde"[6] as int
}

module Regression {
  newtype GoodUint32 = i: int | 0 <= i <
    if "abcrimini"[2 + 1 - 1] == 'c' then
      0x1_0000_0000 + 1 - 1
    else
      3

  // Regression test: The following once crashed, because it had expected
  // the SeqSelect index to really be a folded integer
  newtype NotUint32 = i: int | 0 <= i <
    if "abcrimini"[2 + 1 - 1 + k] == 'c' then
      0x1_0000_0000 + 1 - 1
    else
      3

  const k: int
}

module MoreTests {
  const bv: bv19 := 203

  newtype EmptyFitsIntoUint8 = i: int |
    -0x8000_0000 <= i < if !true then 128 else -0x1_0000_0000 // empty range
    witness *

  newtype int8 = i: int |
    -128 <= i < if !true then -200 else 128

  newtype AnotherInt8 = i: int |
    -128 <= i < if true ==> bv == 203 then 128 else -200

  newtype Int16 = i: int |
    -128 <= i < if true ==> bv == 204 then 128 else 1234
}

module NotJustInequalityConstraints {
  newtype Just7 = x: int | 0 <= x < 256 && x == 7 witness 7 // 7..8
  newtype Just8 = x: int | x == 8 && x == 8 witness 8 // 8..9
  newtype Also8 = x: int | 8 == x && x < 10 && x < 100 && -2 <= x witness 8 // 8..9
  newtype Small = x: int | x < 10 && x < 100 && -2 <= x witness 8 // -2..10
  newtype Only8ButDoesNotDetectCompleteRange = x: int | x == 8 && true witness 8 // 8..9
  newtype Empty = x: int | 8 == x == 7 && 0 <= x < 256 witness * // empty
  newtype Byte = x: int | x in {2, 3, 5} witness 3
  newtype ByteWithKnownRange = x: int | x in {2, 3, 5} && 2 <= x <= 5 witness 3 // 2..6
}
