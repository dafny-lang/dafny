// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Option<T> = None | Some(T)

method Main() {
  var x : Option<(nat, nat)> := Some((2,3));
  var Some((a,b)) := x;
}

method m(x: Option<(nat,nat)>) {
  var Some((a,b)) := x;
}
