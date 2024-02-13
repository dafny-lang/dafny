// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype MyResult = Ok | Err(error: set<string>)
function warningTriggerTest(sr: seq<MyResult>): set<string> {
  set i, err | 0 <= i < |sr| && err in (if sr[i].Err? then sr[i].error else {}) :: err
}