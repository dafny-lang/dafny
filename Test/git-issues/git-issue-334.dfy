// RUN: %exits-with 4 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function method FromAtoB(a: seq<int>): seq<int> {
  // regression: the following had once crashed the translator
  seq(|a|, i => a[i])  // error: index out of bounds
}

function method FromAtoC(a: seq<int>): seq<int> {
  // regression: the following had once crashed the translator
  seq(|a|, i requires 0 <= i < |a| => a[i])
}
