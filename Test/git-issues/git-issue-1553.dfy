// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %exits-with 3 %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Test<R>() {
  var r: R;
  var s: seq<R>;
  var t: array?<R>;
  var u: array<R>;
  var v: (R, int);
}

method Test0<R(0)>() {
  var r: R;
  var s: seq<R>;
  var t: array?<R>;
  var u: array<R>;
  var v: (R, int);
}

method Test00<R(00)>() {
  var r: R;
  var s: seq<R>;
  var t: array?<R>;
  var u: array<R>;
  var v: (R, int);
}
