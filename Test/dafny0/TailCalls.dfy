method {:tailrecursion} A(q: int) returns (x: int, ghost y: bool, z: nat)
{
  if (q < 10) {
    x, y, z := 15, true, 20;
  } else {
    ghost var u;
    x, u, z := A(q-1);
    y := !u;
  }
}

method {:tailrecursion} B(q: int) returns (x: int, ghost y: bool, z: nat)
{
  if (q < 10) {
    x, y, z := 15, true, 20;
  } else {
    ghost var u;
    x, u, z := B(q-1);  // error: not a tail call, because it is followed by an increment to x
    y, x := !u, x + 1;
  }
}

method C(q: int) returns (x: int)
  decreases *;
{
  x := C(q-1);
}

method D(q: int) returns (x: int)
  decreases *;  // error: not allowed, because the method is not tail recursive
{
  x := D(q-1);
  x := x + 1;
}

method E0(q: int) returns (x: int)
  decreases *;  // error: not allowed, because the method is not tail recursive (since mutually recursive methods are currently not recognized as being tail recursive)
{
  x := E1(q-1);
}
method E1(q: int) returns (x: int)
  decreases *;  // error: not allowed, because the method is not tail recursive (since mutually recursive methods are currently not recognized as being tail recursive)
{
  x := E0(q);
}

method F0(q: int) returns (x: int)
  decreases *;  // fine, but no 'decreases' spec is needed at all here
{
  x := D(q);
}
method F1(q: int) returns (x: int)
  decreases 5;  // since this is okay (that is, you can--for no particular reason--add a 'decreases' clause to a non-recursive method), the 'decreases *' above is also allowed
{
  x := D(q);
}

method {:tailrecursion} G0(q: int) returns (x: int)
  decreases *;
{
  x := D(q);
}
method {:tailrecursion false} G1(q: int) returns (x: int)
  decreases *;  // error: even though there is no recursion in this method's body, the annotation specifically says "not tail recursive", so (the easiest thing to do in the Resolver was to) generate an error
{
  x := D(q);
}

method H0(q: int) returns (x: int)
  decreases *;  // fine, but no 'decreases' spec is needed at all here
method {:tailrecursion} H1(q: int) returns (x: int)
  decreases *;  // fine, but no 'decreases' spec is needed at all here
method H2(q: int) returns (x: int)
  decreases 5;  // fine, but no 'decreases' spec is needed at all here
