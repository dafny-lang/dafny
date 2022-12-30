// RUN: %baredafny verify %args --print-tooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Testing constant folding of bit-vector operations
module Main {
  const a: bv8 := 20
  const b: bv8 := 37
  newtype b0 = x | 0 <= x < (a+b) as int
  newtype b1 = x | 0 <= x < (a-b) as int
  newtype b2 = x | 0 <= x < (a*b) as int
  newtype b3 = x | 0 <= x < (b/a) as int
  newtype b4 = x | 0 <= x < (-a+b) as int
  newtype b5 = x | 0 <= x < (b%a) as int
  newtype b6 = x | 0 <= x < (a&b) as int
  newtype b7 = x | 0 <= x < (a^b) as int
  newtype b8 = x | 0 <= x < (a|b) as int
  newtype b9 = x | 0 <= x < (!a) as int
  newtype ba = x | 0 <= x < (if a<b then 24 else 56)
  newtype bb = x | 0 <= x < (if a<=b then 24 else 56)
  newtype bc = x | 0 <= x < (if a>b then 24 else 56)
  newtype bd = x | 0 <= x < (if a>=b then 24 else 56)
  newtype be = x | 0 <= x < (if a==b then 24 else 56)
  newtype bf = x | 0 <= x < (if a!=b then 24 else 56)
  newtype bg = x | 0 <= x < (a<<4) as int
  newtype bh = x | 0 <= x < (b>>1) as int
}

