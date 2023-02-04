// RUN: %baredafny run --no-verify --use-basename-for-filename "%s" > "%t"
// RUN: %baredafny verify --use-basename-for-filename "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var i: int := 42;
  assert {:expect} i == 42;
  print "Done\n";
}
