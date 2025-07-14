method SetInclusionHavoc() {
  ghost var A0: set<(object?, int)> := *;
  ghost var A1: set<(object?, int)> := *;
  assume {:axiom} allocated(A0);
  assume {:axiom} allocated(A1);
  assume {:axiom} forall r: (object?, int) :: r in A0 ==> r in A1;
  assert A0 <= A1; // Failing
}
method SetEqualityHavoc() {
  ghost var A0: set<(object?, int)> := *;
  ghost var A1: set<(object?, int)> := *;
  assume {:axiom} allocated(A0);
  assume {:axiom} allocated(A1);
  assume {:axiom} forall r: (object?, int) :: r in A0 <==> r in A1;
  assert A0 == A1; // Failing
}

method Set() returns (s: set<(object?, int)>)
method SetInclusionMethod() {
  ghost var A0: set<(object?, int)> := Set();
  ghost var A1: set<(object?, int)> := Set();
  assume {:axiom} forall r: (object?, int) :: r in A0 ==> r in A1;
  assert A0 <= A1;
}
method SetEqualityMethod() {
  ghost var A0: set<(object?, int)> := Set();
  ghost var A1: set<(object?, int)> := Set();
  assume {:axiom} forall r: (object?, int) :: r in A0 <==> r in A1;
  assert A0 == A1;
}
