// RUN: %testDafnyForEachResolver "%s" --expect-exit-code=2 --refresh-exit-code=0 -- --relax-definite-assignment

const X := 1

method LegacyTypeSystemCannotInferTypes() {
  var c; // error: type inferred to be int in refresh resolver, but fails in legacy resolver
  match c
  case X => // the literal 1
    assert c == 1;
  case Xyz => // a bound variable
}
