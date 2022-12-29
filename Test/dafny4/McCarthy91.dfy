// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// The usual recursive method for computing McCarthy's 91 function

method Main() {
  var s := [3, 99, 100, 101, 1013];

  var n := 0;
  while n < |s| {
    var m := M(s[n]);
    print "M(", s[n], ") = ", m, "\n";
    n := n + 1;
  }

  n := 0;
  while n < |s| {
    print "mc91(", s[n], ") = ", mc91(s[n]), "\n";
    n := n + 1;
  }

  n := 0;
  while n < |s| {
    var m := Mc91(s[n]);
    print "Mc91(", s[n], ") = ", m, "\n";
    n := n + 1;
  }

  n := 0;
  while n < 5 {
    var m := iter(n, mc91, 40);
    print "iter(", n, ", mc91, 40) = ", m, "\n";
    n := n + 1;
  }
}

method M(n: int) returns (r: int)
  ensures r == if n <= 100 then 91 else n - 10
  decreases 100 - n
{
  if n <= 100 {
    r := M(n + 11);
    r := M(r);
  } else {
    r := n - 10;
  }
}

// Same as above, but as a function

function method mc91(n: int): int
  ensures n <= 100 ==> mc91(n) == 91
  decreases 100 - n
{
  if n <= 100 then
    mc91(mc91(n + 11))
  else
    n - 10
}

// Iterating a function f e times starting from n

function method iter(e: nat, f: int -> int, n: int): int
{
  if e == 0 then n else iter(e-1, f, f(n))
}

// Iterative version of McCarthy's 91 function, following in lockstep
// what the recursive version would do

method Mc91(n0: int) returns (r: int)
  ensures r == mc91(n0)
{
  var e, n := 1, n0;
  while e > 0
    invariant iter(e, mc91, n) == mc91(n0)
    decreases 100 - n + 10 * e, e
  {
    if n <= 100 {
      e, n := e+1, n+11;
    } else {
      e, n := e-1, n-10;
    }
  }
  return n;
}
