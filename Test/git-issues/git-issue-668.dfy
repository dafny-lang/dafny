class X {
  function method F(): int { 2 }
}

class K { }

  method P0(x: X, k: K) {
  var o; // type inferred to be object
  o := x;
  o := k;
  var u := o.F(); // F does not exist in object
}


