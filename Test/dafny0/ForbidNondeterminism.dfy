// RUN: %baredafny verify %args "%s" > "%t" || true
// RUN: %diff "%s.expect" "%t"
// Note, despite the name of this file, this file really tests definite assignment, but see ForbidNondeterminismCompile.dfy.
class C {
  var f: real
}

predicate method P(z: int) { true }

method M(c: C, u: int) returns (r: int)
  modifies c
  decreases *
{
  var x := 3;  // fine
  var y;  // this statement by itself is nondeterministic, but by itself is not an error
  if u < 10 {
    r := y;  // error: nondeterministic value in y
  } else if u < 20 {
    y := 4;
    r := y;  // fine
  } else if u < 30 {
    y := 4;
    y := *;  // compiler error under deterministic rules
    r := y;  // allowed by definite-assignment rules, but the previous line is reported by compiler
  }
  r := x;
}

method OutputParameters0(x: int) returns (s: int, t: int)
{
  return x, x+45;  // yes, this is legal
}

method OutputParameters1(x: int) returns (s: int, t: int)
{
  if x < 100 {
    return;  // error: this may leave s and t undefined
  } else {
    var y := x + s;  // error: this uses s before it may be defined
  }
}  // error: this may leave t undefined (s, too, but it has been checked on all paths leading here)

method DeclWithHavoc()
{
  var a: int := *; // this counts as a definite assignment
  var b: int;  // fine, since b is never used
  var c := a;
}

type PossiblyEmpty = x: int | true witness *

method MoreDeclWithHavoc()
{
  var a: PossiblyEmpty := *; // this does NOT count as a definite assignment for a possibly-empty type
  var b: PossiblyEmpty;  // fine, since b is never used
  var c := a; // error: a is used without being definitely assigned
}

class CK {
  var x: int
  var y: int
  constructor Init() {
    x := 10;
  } // definite-assignment rules allow fields to be left unassigned
}

method ArrayAllocation(n: nat, p: nat, q: nat)
{
  var a := new int[n]; // definite-assignment rules allow array elements to be left unassigned
  var m := new bool[p,q]; // definite-assignment rules allow array elements to be left unassigned
}
