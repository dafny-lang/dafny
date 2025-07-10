// RUN: %testDafnyForEachResolver --expect-exit-code=0 "%s"

method SetInclusionHavoc() {
  ghost var A0: set<(object?, int)> := *;
  ghost var A1: set<(object?, int)> := *;
  assume {:axiom} allocated(A0);
  assume {:axiom} allocated(A1);
  assume {:axiom} forall r: (object?, int) :: r in A0 ==> r in A1;
  assert A0 <= A1; // Should pass after fix
}

method SetEqualityHavoc() {
  ghost var A0: set<(object?, int)> := *;
  ghost var A1: set<(object?, int)> := *;
  assume {:axiom} allocated(A0);
  assume {:axiom} allocated(A1);
  assume {:axiom} forall r: (object?, int) :: r in A0 <==> r in A1;
  assert A0 == A1; // Should pass after fix
}

method Set() returns (s: set<(object?, int)>)

method SetInclusionMethod() {
  ghost var A0: set<(object?, int)> := Set();
  ghost var A1: set<(object?, int)> := Set();
  assume {:axiom} forall r: (object?, int) :: r in A0 ==> r in A1;
  assert A0 <= A1; // This should already pass
}

method SetEqualityMethod() {
  ghost var A0: set<(object?, int)> := Set();
  ghost var A1: set<(object?, int)> := Set();
  assume {:axiom} forall r: (object?, int) :: r in A0 <==> r in A1;
  assert A0 == A1; // This should already pass
}
