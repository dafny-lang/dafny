// RUN: %dafny /compile:3 /coverage:- /spillTargetCode:1 /compileTarget:cs BranchCoverage2.cs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  // we get here 1 time
  var y := M(5);
  y := M(y);
  y := M(y);

  y := N(5);
  y := N(y);
  y := N(y);

  P(5);

  // do else-if correctly
  // if-then-else expressions
  // &&, ||, ==>, <==
  // if-case
  // if *
  // while
  // match
  // beginning of functions, methods, including tail recursion?
  // beginning of forall/exists bodies, set comprehensions, map comprehensions
  // beginning of labmdas
}

method NeverCalled() {
  // we get here 0 times
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
