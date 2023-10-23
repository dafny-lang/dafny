// RUN: %exits-with 4 %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype Even = n: int | exists h :: h * 2 == n



