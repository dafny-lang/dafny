// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type MyInt_Bad = x | 6 <= x witness 5  // error: witness does not satisfy constraint

type MyInt = x | 6 <= x witness 6

newtype MyNewInt = x | 6 <= x witness 6
