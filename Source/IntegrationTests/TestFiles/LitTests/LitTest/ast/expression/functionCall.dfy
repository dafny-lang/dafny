// RUN: ! %verify %s &> "%t"
// RUN: %diff "%s.expect" "%t"

function Callee(x: nat): nat {
  x
}

method Caller(b: bool) {
  var r := Callee(if b then
    10 else
    -10);
}