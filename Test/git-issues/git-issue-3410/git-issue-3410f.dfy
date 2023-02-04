// RUN: %exits-with 2 %baredafny run --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  ghost var i: int := 42;
  assert {:expect} i == 41;
  print "Done\n";
}

method m() {
  ghost var b: bool := true;
  if b { assert {:expect} true; }
}

ghost method mm() {
  assert {:expect} true;
}
