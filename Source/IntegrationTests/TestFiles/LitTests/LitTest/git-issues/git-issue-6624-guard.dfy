// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %exits-with 4 %verify --type-system-refresh:false --general-newtypes:false --general-traits:legacy "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype GuardedStatus = GuardedStatus(ready: bool) {
  predicate IsFailure() requires ready { false }
  function PropagateFailure(): GuardedStatus { this }
  function Extract(): int { 1 }
}

method ReportGuardPreconditionOnce(status: GuardedStatus) returns (out: GuardedStatus) {
  var x: int;
  x, x :- status, 1;
  out := status;
}
