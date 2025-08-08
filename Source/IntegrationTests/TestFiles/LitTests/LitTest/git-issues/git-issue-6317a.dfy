// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file contains variations of types (D1 and D2) having several common supertypes. This had
// once caused various crashes in the resolver.

trait TBase {}
trait TT {}
datatype D1 extends TBase, TT = D1
datatype D2 extends TBase, TT = D2
type SS = t: TT | t is D1 || t is D2 witness *

method NotUnique(b: bool, d1: D1, d2: D2) {
  var r0 := if b then d1 else d2; // error: type of RHS is not unique (error message says d1 and d2 have different types)
  var r1 := (if b then d1 else d2) as TT; // error: type of if-then-else is not unique
  var r2 := (if b then d1 else d2) as TBase; // error: type of if-then-else is not unique
}
