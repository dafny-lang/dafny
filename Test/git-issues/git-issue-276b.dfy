// RUN: %baredafny verify %args --print-tooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Testing constant folding of bool operations
module Main {
  newtype b0 = x | 0 <= x < (if true then 30 else 40)
  newtype b1 = x | 0 <= x < (if false then 30 else 40)
  newtype b2 = x | 0 <= x < (if true && false then 30 else 40)
  newtype b3 = x | 0 <= x < (if true || false then 30 else 40)
  newtype b4 = x | 0 <= x < (if true ==> false then 30 else 40)
  newtype b5 = x | 0 <= x < (if true <== false then 30 else 40)
  newtype b6 = x | 0 <= x < (if true <==> false then 30 else 40)
  newtype b7 = x | 0 <= x < (if true == false then 30 else 40)
  newtype b8 = x | 0 <= x < (if true != false then 30 else 40)
  newtype b9 = x | 0 <= x < (if !false then 30 else 40)
}

