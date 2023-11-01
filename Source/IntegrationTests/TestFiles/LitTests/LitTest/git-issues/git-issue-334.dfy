// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


function FromAtoB(a: seq<int>): seq<int> {
  // regression: the following had once crashed the translator
  seq(|a|, i => a[i])  // error: index out of bounds
}

function FromAtoC(a: seq<int>): seq<int> {
  // regression: the following had once crashed the translator
  seq(|a|, i requires 0 <= i < |a| => a[i])
}
