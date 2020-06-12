// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class X {
  function method F(): int { 2 }
}

class K { }

method P0(x: X, k: K) {
  var o;  // type inferred to be object
  o := x;
  o := k;
  var u := o.F();  // F does not exist in object
}

method P1(x: X, k: K) {
  var o;  
  o := x; 
  var u := o.F();
  o := k;
}

method P2(x: X, k: K) {
  var o;  
  o := x; 
  var u := o.F();  // Now OK
}
