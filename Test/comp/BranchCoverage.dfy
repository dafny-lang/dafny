// RUN: %dafny /compile:3 /coverage:- /spillTargetCode:1 /compileTarget:cs %S/BranchCoverage2.cs "%s" > "%t"
// RUN: %dafny /compile:3 /coverage:- /spillTargetCode:1 /compileTarget:js %S/BranchCoverage3.js "%s" >> "%t"
// RUN: %dafny /compile:3 /coverage:- /spillTargetCode:1 /compileTarget:go %S/BranchCoverage4.go "%s" >> "%t"
// RUN: %dafny /compile:3 /coverage:- /spillTargetCode:1 /compileTarget:java %S/CodeCoverage.java "%s" >> "%t"
// RUN: %dafny /compile:3 /coverage:- /spillTargetCode:1 /compileTarget:py %S/BranchCoverage.py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// The Main method is at the end of this file, because that makes it easier to maintain
// this test file when adding more tests.

// ---------- class constructor ----------

class MyClass {
  constructor () {  // 3 times
  }
}

// ---------- routines that are never called ----------

method NeverCalled() {
  // we get here 0 times
}

function FunctionNeverCalled(): int {
  // we get here 0 times
  75
}

// ---------- if ----------

method M(x: int) returns (y: int) {
  // we get here 3 times
  if x < 10 {
    return x + 20;  // we get here 1 time
  } else if x < 20 {  // note: the location between th "else" and the "if" does not get recorded
    return x + 20;  // we get here 0 times
  } else {
    return 100;  // we get here 2 times
  }
}

method N(x: int) returns (y: int) {
  // we get here 3 times
  y := 100;
  if x < 10 {
    return x + 20;  // we get here 1 time
  } else if x < 20 {  // note: the location between th "else" and the "if" does not get recorded
    return x + 20;  // we get here 0 times
  }  // we get to this implicit else 2 times
}


method P(x: int) {
  // we get here 1 time
  var y := 100;
  if * {
    // we get here 0 times, because the compiler picks the other branch, which is empty
    y := y + 2;
  }  // we get to the implicit else 1 time

  if * {
    // we get here 1 time
  } else {
    // we get here 0 times, because the compiler picks the other branch, which is empty
    y := y + 2;
  }

  // the following if is all ghost, so there are no branch-coverage locations in it
  if x < 2 {
  } else if * {
  }

  if x < 2 {
    // get here 0 times
  } else if * {
    // we get here 0 times
    y := y + 1;
  }  // implicit else: 1 time
}

// ---------- if case ----------

method Q(x: int) returns (y: int) {
  // we get here 3 times

  // the following statement is all ghost, so there are no coverage locations in it
  if {
    case x < 100 =>
    case x < 1000 =>
      assert x < 1_000_000;
    case 50 <= x =>
  }

  if
  case x < 100 =>
    // we get here 1 time
  case x < 1000 =>
    // we get here 1 time, since the compiler lays down the cases in order
    return 8;
  case 50 <= x =>
    // we get here 1 time
}

// ---------- while ----------

method R(x: int) returns (y: int) {
  // we get here 1 time
  var i: nat := 0;
  while i < x {
    // we get here 111 times
    i := i + 1;
  }

  while * {
    // we get here 0 times
    break;
  }

  while
    decreases i
  {
    case i % 2 == 0 =>
      // we get here 56 times
      if i == 0 {
        // we get here 1 time
        break;
      }  // implicit else: 55 times
      i := i - 1;
    case i % 4 == 1 =>
      // we get here 28 times
      i := i - 1;
    case 0 < i =>
      // we get here 28 times
      i := i - 1;
  }

  return 40;
}

// ---------- top-level if-then-else ----------

function Fib(n: nat): nat {
  // we get here 465 times
  if n < 2 then  // then: 233 times
    n
  else if false then  // then: 0 times (else-if is omitted)
    8
  else  // else: 232 times
    Fib(n - 2) + Fib(n - 1)
}

// ---------- top-level match expression, match statement, and tail recursion ----------

function {:tailrecursion} Factorial(n: nat): nat {
  // 11 times
  match n
  case 0 => 1  // 1 time
  case _ => n * Factorial(n - 1)  // 10 times
}

method {:tailrecursion} ComputeFactorial(n: nat, acc: nat) returns (f: nat)
  ensures f == Factorial(n) * acc
{
  // 11 times
  match n
  case 0 =>  // 1 time
    return acc;
  case _ =>  // 10 times
    f := ComputeFactorial(n - 1, acc * n);
}

// ---------- Main ----------

method Main() {
  // we get here 1 time

  var mc := new MyClass();
  mc := new MyClass();
  mc := new MyClass();

  var y := M(5);
  y := M(y);
  y := M(y);

  y := N(5);
  y := N(y);
  y := N(y);

  P(5);

  y := Q(50);
  y := Q(101);
  y := Q(1010);

  y := R(111);

  y := Fib(12);

  y := Factorial(10);
  y := ComputeFactorial(10, 1);
}
