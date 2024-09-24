// RUN: %verify %s &> "%t"
// RUN: %diff "%s.expect" "%t"

method AssignToNat(b: bool) {
  var r: int :| false by {
    assume {:axiom} false;
  }
}