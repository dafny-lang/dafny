// RUN: %exits-with 4 %baredafny verify %args --print-tooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Main {
  newtype b1 = x | 0 <= x < 3/(2-2)
  newtype b2 = x | 0 <= x < 3%(2-2)
  newtype b3 = x | 0 <= x < (3.0/(2.0-2.0)) as int
  newtype b4 = x | 0 <= x < 1.5 as int
  newtype b5 = x | 0 <= x < 1000.0 as bv8 as int
  newtype b6 = x | 0 <= x < 100.5 as bv8 as int
  newtype b8 = x | 0 <= x < 1000 as bv8 as int
  newtype b9 = x | 0 <= x < 1000 as bv16 as bv8 as int
  newtype b10 = x | 0 <= x < -1 as int as char as int
  newtype b11 = x | 0 <= x < -1 as real as char as int
  newtype b12 = x | 0 <= x < 1.5 as real as char as int
  newtype b13 = x | 0 <= x < 'c' as bv2 as int
  newtype b14 = x | 0 <= x < 0xffffff as bv32 as char as int
  newtype b15 = x | 0 <= x < ((10 as bv8)/(0 as bv8)) as int
  newtype b16 = x | 0 <= x < ((10 as bv8)%(0 as bv8)) as int
  newtype b17 = x | 0 <= x < (10 as bv8 << -1) as int
  newtype b18 = x | 0 <= x < (10 as bv8 >> -1) as int

  newtype c0 = x | 0 <= x < 100
  const cc1: c0 := 50
  newtype c1 = x | 0 <= x < 50 as c0 // not constant-folded
  newtype c2 = x: int | 0 <= x < cc1 as int // evaluated

  newtype c3 = x | 0 <= x < "abcde"[6] as int
}

