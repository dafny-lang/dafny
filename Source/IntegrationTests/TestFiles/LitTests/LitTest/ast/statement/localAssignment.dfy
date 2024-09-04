// RUN: ! %verify %s &> "%t"
// RUN: %diff "%s.expect" "%t"

method AssignToNat(b: bool) {
  var r: nat := if b then
    10 else
    -10;
}