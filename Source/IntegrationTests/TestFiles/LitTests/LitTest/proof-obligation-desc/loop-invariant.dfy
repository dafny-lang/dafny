// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method LoopInvariant() {
  var i := 10;
  while 0 <= i
    invariant 0 <= i <= 10
    decreases i
  {
    i := i - 1;
  }
}