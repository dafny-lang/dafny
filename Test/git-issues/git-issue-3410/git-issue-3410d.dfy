// RUN: ! %baredafny run -t:cs --no-verify --use-basename-for-filename "%s" > "%t"
// RUN: ! %baredafny run -t:js --no-verify --use-basename-for-filename "%s" > "%t"
// RUN: ! %baredafny run -t:go --no-verify --use-basename-for-filename "%s" > "%t"
// RUN: ! %baredafny run -t:py --no-verify --use-basename-for-filename "%s" > "%t"
// RUN: ! %baredafny run -t:java --no-verify --use-basename-for-filename "%s" > "%t"
// RUN: %exits-with 4 %baredafny verify --use-basename-for-filename "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var i: int := 42;
  assert {:expect} i == 41;
  print "Done\n";
}
