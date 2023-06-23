// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment
//
// This fragment of comp/Calls.dfy serves to facilitate incremental compiler development.

function F(x: int, y: bool): int {
  x + if y then 2 else 3
}

method Main() {
  var w;
  w := F(2, false);
  print w, "\n";
}
