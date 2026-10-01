// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation --allow-deprecation --unicode-char false

// Function values (lambdas) on the c++ backend. Uses native newtypes only, since the
// c++ target still rejects unbounded `int`; a lambda over `int` would be rejected for
// the `int` itself, independent of the function-value support added here.

newtype i32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method Main() {
  // A function value stored in a variable and applied.
  var inc: i32 -> i32 := (n: i32) => if n < 0x7fff_ffff then n + 1 else n;
  print inc(41), "\n";             // 42

  // A predicate (lambda returning bool).
  var pos: i32 -> bool := (n: i32) => n > 0;
  print pos(4), " ", pos(-7), "\n";   // true false

  // Two arguments, with a bool lambda to avoid overflow reasoning.
  var eq: (i32, i32) -> bool := (a: i32, b: i32) => a == b;
  print eq(21, 21), " ", eq(21, 22), "\n";   // true false

  // A function value passed to and returned from another function.
  var twice := ApplyTwice(inc, 40);
  print twice, "\n";               // 42
}

function ApplyTwice(f: i32 -> i32, x: i32): i32 {
  f(f(x))
}
