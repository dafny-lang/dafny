// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type T
datatype BaseType = BaseType(t: T)

predicate P(d: BaseType)
type SubsetType = d: BaseType | P(d) witness *

method m0(dp: SubsetType)

method m1(dp: SubsetType, t: T) {
  var dp': SubsetType := [dp][0].(t := t); // Error: `t` does not satisfy subtype constraints
}
