// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function F0(older x: int): int // error: only predicates support 'older' parameters
twostate function F1(older x: int): int // error: only predicates support 'older' parameters

function G0(older x: int): bool
predicate G1(older x: int)
function method G2(older x: int): bool
predicate method G3(older x: int)
twostate function G4(older x: int): bool
twostate predicate G5(older x: int)

predicate H0(older x: int, older y: int)
