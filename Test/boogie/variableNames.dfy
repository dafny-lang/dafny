// RUN: %dafny /compile:0 /env:0 /print:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
method M(heap: object) 
  modifies heap
{
  var x := 0; // x#0
  if y :| y < x {
    var x := 0; 
  } else {
    var y := 0;
  }
  
  while(x < 5) {
    var x:= 2;
    var y := 0;
  }
  
  for i: int := 0 to 3 {
    var x:= 2;
    var y := 0;
  }
  
  forall i | 0 <= i < x {
    var x:= 2;
    var y := 0;
  }
  
  var s := {2,3};
  modify heap {
    var z := 3; // modify does not push a Dafny scope, so we can't assign to a fresh x here.
  }
  
  assert x == 0 by {
    var x := x + 2;
    var y := 0;
  }
  var y := 200;
}