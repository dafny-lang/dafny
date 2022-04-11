// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
//
// This fragment of comp/Calls.dfy serves to facilitate incremental compiler development.

method Main()
{
  VariableCapture.Test();
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
