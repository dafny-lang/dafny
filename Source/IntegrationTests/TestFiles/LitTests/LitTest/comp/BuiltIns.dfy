// RUN: %testDafnyForEachCompiler "%s"

// Essentially a copy of DafnyRuntime/systemModulePopulator.dfy,
// but here independently as a test that all the implicitly-referenced built-ins
// are in fact correctly added to the runtimes.

method HasTuples() {
  var b := true;
  var has0 := ();
  var has1 := (b, ghost b);  // Just (1) is an bool in parentheses instead
  var has2 := (b,b);
  var has3 := (b,b,b);
  var has4 := (b,b,b,b);
  var has5 := (b,b,b,b,b);
  var has6 := (b,b,b,b,b,b);
  var has7 := (b,b,b,b,b,b,b);
  var has8 := (b,b,b,b,b,b,b,b);
  var has9 := (b,b,b,b,b,b,b,b,b);
  var has10 := (b,b,b,b,b,b,b,b,b,b);
  var has11 := (b,b,b,b,b,b,b,b,b,b,b);
  var has12 := (b,b,b,b,b,b,b,b,b,b,b,b);
  var has13 := (b,b,b,b,b,b,b,b,b,b,b,b,b);
  var has14 := (b,b,b,b,b,b,b,b,b,b,b,b,b,b);
  var has15 := (b,b,b,b,b,b,b,b,b,b,b,b,b,b,b);
  var has16 := (b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b);
  var has17 := (b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b);
  var has18 := (b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b);
  var has19 := (b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b);
  var has20 := (b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b);
}

method HasArrows() {
  var has0 := () => 42;
  var has1 := (x1: bool) => 42;
  var has2 := (x1: bool, x2: bool) => 42;
  var has3 := (x1: bool, x2: bool, x3: bool) => 42;
  var has4 := (x1: bool, x2: bool, x3: bool, x4: bool) => 42;
  var has5 := (x1: bool, x2: bool, x3: bool, x4: bool, x5: bool) => 42;
  var has6 := (x1: bool, x2: bool, x3: bool, x4: bool, x5: bool, x6: bool) => 42;
  var has7 := (x1: bool, x2: bool, x3: bool, x4: bool, x5: bool, x6: bool, x7: bool) => 42;
  var has8 := (x1: bool, x2: bool, x3: bool, x4: bool, x5: bool, x6: bool, x7: bool, x8: bool) => 42;
  var has9 := (x1: bool, x2: bool, x3: bool, x4: bool, x5: bool, x6: bool, x7: bool, x8: bool, x9: bool) => 42;
  var has10 := (x1: bool, x2: bool, x3: bool, x4: bool, x5: bool, x6: bool, x7: bool, x8: bool, x9: bool, x10: bool) => 42;
  var has11 := (x1: bool, x2: bool, x3: bool, x4: bool, x5: bool, x6: bool, x7: bool, x8: bool, x9: bool, x10: bool, x11: bool) => 42;
  var has12 := (x1: bool, x2: bool, x3: bool, x4: bool, x5: bool, x6: bool, x7: bool, x8: bool, x9: bool, x10: bool, x11: bool, x12: bool) => 42;
  var has13 := (x1: bool, x2: bool, x3: bool, x4: bool, x5: bool, x6: bool, x7: bool, x8: bool, x9: bool, x10: bool, x11: bool, x12: bool, x13: bool) => 42;
  var has14 := (x1: bool, x2: bool, x3: bool, x4: bool, x5: bool, x6: bool, x7: bool, x8: bool, x9: bool, x10: bool, x11: bool, x12: bool, x13: bool, x14: bool) => 42;
  var has15 := (x1: bool, x2: bool, x3: bool, x4: bool, x5: bool, x6: bool, x7: bool, x8: bool, x9: bool, x10: bool, x11: bool, x12: bool, x13: bool, x14: bool, x15: bool) => 42;
  var has16 := (x1: bool, x2: bool, x3: bool, x4: bool, x5: bool, x6: bool, x7: bool, x8: bool, x9: bool, x10: bool, x11: bool, x12: bool, x13: bool, x14: bool, x15: bool, x16: bool) => 42;
}

newtype byte = x: int | 0 <= x < 256

method HasArrays() {
  var n: byte := 0;
  var has1 := new bool[n];
  var has2 := new bool[n,n];
  var has3 := new bool[n,n,n];
  var has4 := new bool[n,n,n,n];
  var has5 := new bool[n,n,n,n,n];
  var has6 := new bool[n,n,n,n,n,n];
  var has7 := new bool[n,n,n,n,n,n,n];
  var has8 := new bool[n,n,n,n,n,n,n,n];
  var has9 := new bool[n,n,n,n,n,n,n,n,n];
  var has10 := new bool[n,n,n,n,n,n,n,n,n,n];
  var has11 := new bool[n,n,n,n,n,n,n,n,n,n,n];
  var has12 := new bool[n,n,n,n,n,n,n,n,n,n,n,n];
  var has13 := new bool[n,n,n,n,n,n,n,n,n,n,n,n,n];
  var has14 := new bool[n,n,n,n,n,n,n,n,n,n,n,n,n,n];
  var has15 := new bool[n,n,n,n,n,n,n,n,n,n,n,n,n,n,n];
  var has16 := new bool[n,n,n,n,n,n,n,n,n,n,n,n,n,n,n,n];
}

method Main() {
  HasTuples();
  HasArrows();
  HasArrays();
}
