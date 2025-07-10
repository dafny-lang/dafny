method Test() {
  ghost var A0: set<int>;
  ghost var A1: set<int>;
  A0 := *;
  A1 := *;
  assume {:axiom} forall r: int :: r in A0 <==> r in A1;
  assert A0 == A1; // This should pass if the fix works
}
