// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method m() {

  var a: array<nat> := new nat[10];
  var b: array<int> := new int[10];
  b := a;
  a := b;
  mm(b, a);
  print "Done\n";
}

method mm(x: array<nat>, y: array<int>) {}
