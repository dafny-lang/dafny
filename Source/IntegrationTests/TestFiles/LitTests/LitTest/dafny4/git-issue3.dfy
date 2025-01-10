// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype Even = n: int | exists h :: h * 2 == n



