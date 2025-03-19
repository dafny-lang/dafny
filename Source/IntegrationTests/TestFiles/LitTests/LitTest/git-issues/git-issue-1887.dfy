// RUN: %exits-with 2 %build --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function selectOneConstraint<T>(s: seq<T>): seq<string> {
  if |s| == 0 then []
  else [s[0]] + selectOneConstraint(s[1..])
}

function selectManyConstraint<T>(s: seq<T>): seq<string> {
  if |s| <= 1 then []
  else s[0..2] + selectManyConstraint(s[2..])
}
