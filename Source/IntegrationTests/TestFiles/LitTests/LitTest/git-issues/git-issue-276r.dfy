// RUN: %verify --show-hints --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Testing constant folding of real operations
module Main {
  newtype b0 = x | 0 <= x < (2.0+3.0) as int
  newtype b1 = x | 0 <= x < (3.0-2.0) as int
  newtype b2 = x | 0 <= x < (3.0*2.0) as int
  newtype b3 = x | 0 <= x < (4.0/2.0) as int
  newtype b4 = x | 0 <= x < (4.0 + (-2.0)) as int
  newtype b5 = x | 0 <= x < 1000 as real as int
  newtype b6 = x | 0 <= x < 'c' as real as int
  newtype b7 = x | 0 <= x < 2000 as bv16 as real as int
  newtype b8 = x | 0 <= x < 20 as char as int
  newtype b9 = x | 0 <= x < 20 as bv8 as int
  newtype b10 = x | 0 <= x < 30.0 as real as int
  newtype b11 = x | 0 <= x < (if 2.0<3.0 then 35 else 40)
  newtype b12 = x | 0 <= x < (if 3.0<=3.0 then 35 else 40)
  newtype b13 = x | 0 <= x < (if 2.0>3.0 then 35 else 40)
  newtype b14 = x | 0 <= x < (if 2.0>=3.0 then 35 else 40)
  newtype b15 = x | 0 <= x < (if 2.0==3.0 then 35 else 40)
  newtype b16 = x | 0 <= x < (if 2.0!=3.0 then 35 else 40)
}

