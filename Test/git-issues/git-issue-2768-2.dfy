// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type T

type T' = v: T | true witness *

datatype NeverEq' = NeverEq'(T')

type T_NeverEq'(==) = NeverEq'
