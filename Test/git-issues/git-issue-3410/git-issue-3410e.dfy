// RUN: %exits-with 2 %baredafny run --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  ghost var i: int := 42;
  assert i == 41;
  expect i == 41;
  print "Done\n";
}
