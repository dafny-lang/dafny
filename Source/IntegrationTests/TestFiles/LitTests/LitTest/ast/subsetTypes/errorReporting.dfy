// RUN: ! %verify %s &> "%t"
// RUN: %diff "%s.expect" "%t"

type ten = x: int | x == 10 witness if true then
  11 else
  10