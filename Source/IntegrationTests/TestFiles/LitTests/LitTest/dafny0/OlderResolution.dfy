// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


ghost function F0(older x: int): int // error: only predicates support 'older' parameters
twostate function F1(older x: int): int // error: only predicates support 'older' parameters

ghost function G0(older x: int): bool
ghost predicate G1(older x: int)
function G2(older x: int): bool
predicate G3(older x: int)
twostate function G4(older x: int): bool
twostate predicate G5(older x: int)

ghost predicate H0(older x: int, older y: int)
