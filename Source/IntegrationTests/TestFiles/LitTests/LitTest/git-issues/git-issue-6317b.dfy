// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file contains variations of types (D1 and D2) having several common supertypes. This had
// once caused various crashes in the resolver.

trait TBase {}
trait TT {}
datatype D1 extends TBase, TT = D1
datatype D2 extends TBase, TT = D2
type SS = t: TT | t is D1 || t is D2 witness *

method Fine(b: bool, d1: D1, d2: D2) {
  var r0: TT := if b then d1 else d2;
  var r1: TBase := if b then d1 else d2;
  var r2 := if b then d1 as TBase else d2;
  var r3 := if b then d1 else d2 as TBase;
  var r4 := if b then d1 as TT else d2;
  var r5 := if b then d1 else d2 as TT;

  var s0 := if b then d1 as SS else d2;
  var s1 := if b then d1 as SS else d2 as SS;
}

function F0(b: bool, d1: D1, d2: D2): TT {
  if b then d1 else d2
}

function F1(b: bool, d1: D1, d2: D2): TBase {
  if b then d1 else d2
}

function F2(b: bool, d1: D1, d2: D2): TT {
  if b then d1 else d2 as SS
}

function F3(b: bool, d1: D1, d2: D2): TT {
 if b then d1 else d2 as TT
}
