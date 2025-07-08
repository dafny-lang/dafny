// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

method Match(tp: (nat, nat)) {
  match tp
  case (0, _) => print "match", "\n";
  case _ =>
} 

method {:tailrecursion true} Countdown(x: nat) {
  label here: {
    if x == 0 {
      print "Kablammo!!\n";
    } else {
      print x, "\n";
      Countdown(x - 1);
    }
  }
}

datatype A = A(val: int)

method LetExpr() {
  print (var a := A(0); var A(zero) := a; zero), "\n";
}

function f(i: int): int {
  i + 1
}

function F(i: int): int -> int {
  j => j + i + 1
}

method SequenceConstructionWithNamedFunction(){
  var g := (i => i+1);
  print seq(10, f), "\n";
  print seq(10, g), "\n";
  print seq(10, F(0)), "\n";
}

method Main() {
  Match((0,1));
  Countdown(1);
  LetExpr();
  SequenceConstructionWithNamedFunction();
}
