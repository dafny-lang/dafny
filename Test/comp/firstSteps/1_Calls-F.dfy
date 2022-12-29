// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=py "%s" "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
//
// This fragment of comp/Calls.dfy serves to facilitate incremental compiler development.

function method F(x: int, y: bool): int {
  x + if y then 2 else 3
}

method Main() {
  var w;
  w := F(2, false);
  print w, "\n";
}
