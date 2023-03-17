// RUN: ! %baredafny resolve --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = B | CCC | E { predicate IsFailure() { E? } function PropagateFailure(): D { E } }

// Careful: some errors will prevent subsequent ones from begin reported

method m2() returns (d: D) {
  var x := (var y, z :- D.E; 0);
  var x := (var y :- D.CCC, 0; 0);
  var x := (var y = D.CCC, 0; 0);
  var x := (var B() :| D.CCC; 0);
  var m := map x, y :: x+y;
  var n := ( z := 0 );
  var s := seq<int,int>[1,2,3];
}

method m3() {
  var x := (var x ^:= 0; 0);
}

