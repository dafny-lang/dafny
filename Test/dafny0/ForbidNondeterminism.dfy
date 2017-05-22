// RUN: %dafny /compile:1 /deterministic "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var f: real
}

predicate method P(z: int) { true }

method M(c: C)
  requires c != null
  modifies c
  decreases *
{
  var x := 3;  // fine
  var y;  // error: this statement by itself is nondeterministic
  y := 4;
  y := *;  // error: nondeterministic
  x, y := x, *;  // error: nondeterministic
  y :| true;  // error: nondeterministic
  if * {  // error: nondeterministic //----------------------BUG
    x := x + 1;
  }
  if {  // error: nondeterministic //----------------------BUG
    case true =>  x := x + 1;
  }
  if z :| 10 <= z < 15 && P(z) {  // error: nondeterministic
    x := z;
  }
  while *  // error: nondeterministic
    decreases *
  {
    x := x + 1;
  }
  while  // error: nondeterministic
    decreases if x <= 100 then 100-x else x
  {
    case x < 100 => x := x + 1;
    case 100 < x => x := x - 1;
  }
  var a := new int[100];
  forall i | 0 <= i < a.Length {
    a[i] := *;  // error: nondeterministic
  }
  modify c;  // error: nondeterministic
  modify c {  // fine
  }
}
