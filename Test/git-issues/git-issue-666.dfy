// RUN: %exits-with 2 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait O {
  function method F(): int { 2 }
}
class X extends O { }
class Y extends O { }

method M0() {
  var o;  // type inferred to be O
  o := new X;
  o := new Y;
  var u := o.F();  // this once crashed the type checker
}

method M1() {
  var o := null;  // type inferred to be O?
  o := new X;
  o := new Y;
  var u := o.F();  // this once crashed the type checker
}

method M2(x: X) {
  var o;  // type inferred to be O
  o := x;
  o := new Y;
  var u := o.F();  // this once crashed the type checker
}

method M3(x: X?) {
  var o;  // type inferred to be O?
  o := x;
  o := new Y;
  var u := o.F();
}

class K { }

/*
method P0() {
  var o;  // type inferred to be object
  o := new X;
  o := new K;
  var u := o.F();  // F does not exist in object (this once crashed the type checker)
}

method P1() {
  var o := null;  // type inferred to be object?
  o := new X;
  o := new K;
  var u := o.F();  // F does not exist in object (this once crashed the type checker)
}

method P2(x: X) {
  var o;  // type inferred to be object
  o := x;
  o := new K;
  var u := o.F();  // F does not exist in object (this once crashed the type checker)
}
*/

method P3(x: X?) {
  var o;  // type inferred to be object?
  o := x;
  o := new K;
  var u := o.F();  // F does not exist in object
}
