// RUN: ! %baredafny build %args --enforce-determinism "%s" --target cs > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var f: real
}

predicate P(z: int) { true }

method M(c: C)
  modifies c
  decreases *
{
  var x := 3;  // fine
  var y;  // this statement by itself is nondeterministic, but the verifier catches bad uses of "y"
  y := 4;
  y := *;  // error: nondeterministic
  x, y := x, *;  // error: nondeterministic
  y :| true;  // error: nondeterministic
  if * {  // error: nondeterministic
    x := x + 1;
  }
  if {  // error: nondeterministic
    case true =>  x := x + 1;
    case true =>  x := x + 2;
  }
  if c.f < 500.0 {
    if {  // a one-case if is always deterministic
      case c.f < 1000.0 => x := x + 1;
    }
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
  var a := new int[100](_ => 750);
  forall i | 0 <= i < a.Length {
    a[i] := *;  // error: nondeterministic
  }
  modify c;  // error: nondeterministic
  modify c {  // fine
  }
}

method OutputParameters0(x: int) returns (s: int, t: int)
{
  return x, x+45;  // yes, this is legal
}


method DeclWithHavoc()
{
  var b: int := *;  // error: technically fine, since b is never used, but here the compiler
                    // checking is overly conservative
}

iterator IterWeird() yields ()  // no yields parameters, so allowed
{
}

iterator Iter() yields (x: int)  // error: not allowed by determinism rules
{
}
