// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method m() {

  var a: array<nat> := new nat[10];
  var b: array<int> := new int[10];
  b := a; // type error expected
  a := b; // type error expected
  mm(b, a);
}

method mm(x: array<nat>, y: array<int>) {}

method q() {

  var a: seq<nat>;
  var b: seq<int>;
  b := a; // but OK for value types
  a := b; // but OK for value types
  qq(b, a);
}

method qq(x: seq<nat>, y: seq<int>) {}
