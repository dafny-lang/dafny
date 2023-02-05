// RUN: %baredafny verify --use-basename-for-filename "%s" > "%t"
// RUN: %baredafny run -t:cs --use-basename-for-filename --no-verify "%s" >> "%t"
// RUN: %baredafny run -t:js --use-basename-for-filename --no-verify "%s" >> "%t"
// RUN: %baredafny run -t:go --use-basename-for-filename --no-verify "%s" >> "%t"
// RUN: %baredafny run -t:py --use-basename-for-filename --no-verify "%s" >> "%t"
// RUN: %baredafny run -t:java --use-basename-for-filename --no-verify "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var i: int := 42;
  assert {:expect} i == 42;
  print "Done\n";
}
