// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

method Main() { }
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
