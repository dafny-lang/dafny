// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var four := Four();
  print "four is ", four, "\n"; // 4
  print "Recursive(7) = ", Recursive(7), "\n"; // 14
  print "NonCompilableFunction: ", NonCompilableFunction(2), " ", NonCompilableFunction(4), "\n"; // 4 7
  var s, s' := {2, 7, 5}, {2, 0, 2, 1};
  print "Sums: ", Sum(s), " ", Sum(s'), "\n";
}

function Four(): int {
  4
} by method {
  // The print statement in Dafny is effectful, but it has no specification that
  // says whether or not to expect such an effect. In that sense, print is best treated
  // as a debugging feature. Here, it's used in a by-method, which means it will be
  // printed as when the caller calls a function--something that does not happen elsewhere
  // in the language.
  print "hello\n";
  return 2 + 2;
}

function Recursive(n: nat, acc: nat := 0): nat {
  2 * n + acc
} by method { // compiled as tail recursive
  if n == 0 {
    return acc;
  } else {
    return Recursive(n - 1, acc + 2);
  }
}

function NonCompilableFunction(n: nat): (r: nat) {
  // This function body cannot be compiled, since it mentions a least predicate.
  // That's fine, as long as the compiler doesn't incorrectly try to compile the
  // function body.
  if P(n) then n + 2 else n + 3
} by method {
  AboutP(n);
  r := if n <= 3 then n + 2 else n + 3;
}

least predicate P(x: int) {
  x == 3 || P(x + 1)
}

lemma AboutP(x: int)
  ensures P(x) <==> x <= 3
{
  if P(x) {
    Ping(x);
  }
  if x <= 3 {
    Pong(x);
  }
}

least lemma Ping(x: int)
  requires P(x)
  ensures x <= 3
{
}

lemma Pong(x: int)
  requires x <= 3
  ensures P(x)
  decreases 3 - x
{
  if x < 3 {
    Pong(x + 1);
  }
}

// ------------------ longer example ------------------
// This example sums the elements of a set. Because summing
// is associate and commutative, the order in which the elements
// are drawn from the set does not matter. The implementation
// below is efficient, except for the part that tracks what
// elements have already been picked from the set (an inefficiency
// that will be solved once Dafny supports built-in iterations
// over sets).

function Sum(s: set<int>): int {
  if s == {} then 0 else
    var x := Pick(s);
    x + Sum(s - {x})
} by method {
  var sum := 0;
  var s' := s;
  while s' != {}
    invariant s' <= s
    invariant sum + Sum(s') == Sum(s)
  {
    var x :| x in s';
    var s'' := s' - {x};
    assert s'' + {x} == s';
    SumLemma(s'', x);
    sum, s' := sum + x, s'';
  }
  return sum;
}

function Pick(s: set<int>): int
  requires s != {}
{
  var x :| x in s; x
}

lemma SumLemma(s: set<int>, y: int)
  requires y !in s
  ensures Sum(s + {y}) == Sum(s) + y
{
  if s == {} {
  } else {
    var sy := s + {y};
    assert s == sy - {y};
    var x := Pick(sy);
    if x == y {
    } else {
      var s'x := s - {x};
      assert s'x + {x} == s;
      calc {
        Sum(s + {y});
      ==
        Sum(sy);
      ==  // def. Sum
        x + Sum(sy - {x});
      ==  { assert sy - {x} == s'x + {y}; }
        x + Sum(s'x + {y});
      ==  { SumLemma(s'x, y); }
        x + Sum(s'x) + y;
      ==  { SumLemma(s'x, x); }
        Sum(s'x + {x}) + y;
      ==
        Sum(s) + y;
      }
    }
  }
}
