// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// :older attributes on non-functions are ignored
method {:older x, y} M(x: int) returns (y: int)

function {:older x} F0(x: int): int // error: :older is allowed only on predicates
twostate function {:older x} F1(x: int): int // error: :older is allowed only on predicates
least predicate {:older x} F2(x: int) // error: :older is allowed only on predicates
greatest predicate {:older} F3(x: int) // error: :older is allowed only on predicates

function {:older x} G0(x: int): bool
predicate {:older x} G1(x: int)
function method {:older x} G2(x: int): bool
predicate method {:older x} G3(x: int)
twostate function {:older x} G4(x: int): bool
twostate predicate {:older x} G5(x: int)

predicate {:older x, y} H0(x: int, y: int)
predicate {:older x, y, x} H1(x: int, y: int) // error: x is duplicated
predicate {:older} H2(x: int, y: int) // error: no arguments are listed
predicate {:older x + y} H3(x: int, y: int) // error: arguments are expected to be formals
predicate {:older ((x)), (y)} H4(x: int, y: int)

class C {
  predicate {:older this} Instance0(x: int)
  predicate {:older x, this} Instance1(x: int)
  predicate {:older x, this, this} Instance2(x: int) // error: "this" is duplicated
}
