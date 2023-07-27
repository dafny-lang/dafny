// RUN: %exits-with 2 %baredafny test --show-snippets:false --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method {:extern} {:test} m(i: int, ghost j: int) 
  requires j == 1
