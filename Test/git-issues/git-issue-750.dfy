// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method m() {

  var a: array<nat> := new nat[10];
  var b: array<int> := new int[10];
  b := a;
  a := b;
  mm(b, a);
}

method mm(x: array<nat>, y: array<int>) {}

method q() {

  var a: seq<nat>;
  var b: seq<int>;
  b := a;
  a := b;
  qq(b, a);
}

method qq(x: seq<nat>, y: seq<int>) {}
