// RUN: %baredafny verify %args --print-tooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Testing constant folding of char, string operations
module Main {
  const s := "abcde"
  const c := s[4]
  newtype b0 = x | 0 <= x < |s+s|
  newtype b1 = x | 0 <= x < c as int
  newtype b2 = x | 0 <= x < c as bv8 as int
  newtype b3 = x | 0 <= x < 20 as char as int
  newtype b4 = x | 0 <= x < 200 as bv8 as char as int
  newtype b5 = x | 0 <= x < ( if 'a' == c then 30 else 40 )
  newtype b6 = x | 0 <= x < ( if 'a' != c then 30 else 40 )
  newtype b7 = x | 0 <= x < ( if 'a' <= c then 30 else 40 )
  newtype b8 = x | 0 <= x < ( if 'a' <  c then 30 else 40 )
  newtype b9 = x | 0 <= x < ( if 'a' >=  c then 30 else 40 )
  newtype ba = x | 0 <= x < ( if 'a' >   c then 30 else 40 )
  newtype bb = x | 0 <= x < ( if s == s then 30 else 40 )
  newtype bc = x | 0 <= x < ( if s != s then 30 else 40 )
  newtype bd = x | 0 <= x < ( if s <= s then 30 else 40 )
  newtype be = x | 0 <= x < ( if s <  s then 30 else 40 )
  newtype bf = x | 0 <= x < ( if s <= s+s then 30 else 40 )
  newtype bg = x | 0 <= x < ( if s <  s+s then 30 else 40 )
}

