// RUN: %exits-with 1 %baredafny run --no-verify --use-basename-for-filename "%s" > "%t"
// RUN: %exits-with 4 %baredafny verify --use-basename-for-filename "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var i: int := 42;
  assert i == 41;
  expect i == 41;
  print "Done\n";
}
