// RUN: %verify %s --standard-libraries=true &> "%t"
// RUN: %diff "%s.expect" "%t"

import opened Std.Wrappers

method ByWellformedness(x: int) returns (r: Option<int>) {
  var p: int :- Some(3 / x) by {
    assume {:axiom} x > 0;
  }
  var q: int :- None;
  r := Some(4);
}