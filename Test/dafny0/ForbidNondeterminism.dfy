// RUN: %baredafny verify %args "%s" > "%t" || true
// RUN: %diff "%s.expect" "%t"

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
  var a: int := *;
  var b: int := *;  // fine, since b is never used
  var c := a;  // error: a is used before given a definite value
}

class CK {
  var x: int
  var y: int
  constructor Init() {
    x := 10;
  }  // error: value of y left nondeterministic
}

method ArrayAllocation(n: nat, p: nat, q: nat)
{
  var a := new int[n];  // error: the array elements will be assigned nondeterministically
  var m := new bool[p,q];  // error: the matrix elements will be assigned nondeterministically
}
