// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

function F(x: int, y: bool): int {
  x + if y then 2 else 3
}

method A0(x: int, y: bool) {
  return;
}

method A1(x: int, y: bool) returns (a: int) {
  return a;
}

method A2(x: int, y: bool) returns (a: int, b: bool) {
  return a, b;
}

method A3(x: int, y: bool) returns (a: int, b: bool, c: int) {
  var u;
  if x == 3 {
    u := c;
  } else if x == 4 {
    u := c + 0;
  } else {
    u := c + 0 + 0;
  }
  u := 1 * u;
  {
    var y := 65;
    u := 0 + u;
  }
  return a, b, u;
}

method Main()
{
  var w, a, b, c, d, e, f;
  w := F(2, false);
  A0(2, false);
  a := A1(2, false);
  b, c := A2(2, false);
  d, e, f := A3(2, false);
  print w, " ", a, " ", b, " ", c, " ", d, " ", e, " ", f, "\n";

  FunctionValues.Test();
  VariableCapture.Test();
}

module FunctionValues {
  method Test() {
    var c := new Class(5);
    var color := Red;
    var nt: NT := 5;
    ApplyAndPrint(c.F);
    ApplyAndPrint(c.G);
    ApplyAndPrint(color.F);
    ApplyAndPrint(color.G);
    ApplyAndPrint(nt.F);
    ApplyAndPrint(nt.G);
    print "\n";
    // test variable capture
    var x0, x1, x2, x3, x4, x5 := c.F, c.G, color.F, color.G, nt.F, nt.G;
    c := new Class(2);
    color, nt := Blue, 2;
    print x0(), " ", x1(), " ", x2(), " ", x3(), " ", x4(), " ", x5(), "\n";
  }

  method ApplyAndPrint(f: () -> int) {
    print f(), " ";
  }

  class Class {
    const x: int
    constructor (x: int) { this.x := x; }
    function F(): int { x }
    static ghost function G(): int { 3 }
  }

  datatype Color = Red | Green | Blue {
    function F(): int { if this == Red then 5 else 2 }
    static ghost function G(): int { 3 }
  }

  newtype NT = x | 0 <= x < 15 {
    function F(): int { this as int }
    static ghost function G(): int { 3 }
  }
}

module VariableCapture {
  method Test() {
    var f, _ := Capture(15);
    print f(), "\n";
    var u, _ := SetToSeq({4, 2, 0} + {2, 1});
    print u, "\n";
    var v, _ := MapToSeq(map[4 := 100, 0 := 300, 2 := 200]);
    print v, "\n";

    var five := 5;
    var gimmieFive := () => five;
    five := 3;
    print "--> ", gimmieFive(), " <--\n";  // 5
  }

  method Capture(x: int) returns (f: () -> int, g: int) {
    g := x;
    f := () => g;
  }

  method SetToSeq(S: set<nat>) returns (r: seq<nat>, g: int) {
    if S == {} {
      r := [];
      return;
    }
    // Most target languages have no immediate match for the expressions in the following
    // lines so the compilation strategies will be informed by the constraints imposed by
    // the target language.
    var x :| x in S;
    g := x;  // In C#, "g" will be a formal out-parameter
    // C# does not allow formal out-parameters to be captured in a lambda, so "g" is saved
    // away in the following line:
    var smaller := set y | y in S && y < g;
    // The "x" in the following line does not need to be saved away in C# (because "x" is
    // a local variable, not an out-parameter). (However, the C# target code currently
    // saves it away needlessly.) In Java, "x" (as well as "g" above) needs to be saved
    // away.
    var larger := set y | y in S && x < y;

    var s, _ := SetToSeq(smaller);
    var l, _ := SetToSeq(larger);
    r := s + [x] + l;
  }

  method MapToSeq(M: map<nat, int>) returns (r: seq<nat>, g: int) {
    if M == map[] {
      r := [];
      return;
    }
    // Most target languages have no immediate match for the expressions in the following
    // lines so the compilation strategies will be informed by the constraints imposed by
    // the target language.
    var x :| x in M.Keys;
    g := x;  // In C#, "g" will be a formal out-parameter
    // C# does not allow formal out-parameters to be captured in a lambda, so "g" is saved
    // away in the following line:
    var smaller := map y | y in M.Keys && y < g :: M[y];
    // The "x" in the following line does not need to be saved away in C# (because "x" is
    // a local variable, not an out-parameter). (However, the C# target code currently
    // saves it away needlessly.) In Java, "x" (as well as "g" above) needs to be saved
    // away.
    var larger := map y | y in M.Keys && x < y :: M[y];

    var s, _ := MapToSeq(smaller);
    var l, _ := MapToSeq(larger);
    r := s + [x] + l;
  }
}
