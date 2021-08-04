// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var four := Four();
  print "four is ", four, "\n"; // 4
  print "Recursive(7) = ", Recursive(7), "\n"; // 14
  print "NonCompilableFunction: ", NonCompilableFunction(2), " ", NonCompilableFunction(4), "\n"; // 4 7
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
