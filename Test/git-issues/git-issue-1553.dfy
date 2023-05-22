// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

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
