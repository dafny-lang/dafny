// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method M() returns (x: int) {
  x := var y := 50; y;  // non-top-level let
}

function method F(): int {
  var r := 58; r  // top-level let
}

method Main() {
  var m := M();
  var f := F();
  print m, " ", f, "\n";

  var t := Node(Node(Leaf, 5, Node(Leaf, 7, Leaf)), 9, Node(Leaf, 10, Node(Leaf, 12, Node(Leaf, 30, Leaf))));
  print t, "\n";
  var s := Sum(t);
  InorderPrint(t);
  print "\n";

  // nested patterns
  var Node(Node(_, y, right), _, Right) := t;
  print y, " ", right.val, "\n";  // 5 7
  var (u0, u1) := var Node(Node(_, xy, xright), _, xRight) := t; (xy, xright);
  print u0, " ", u1.val, "\n";  // 5 7

  Regressions.Test();
}

datatype Tree = Leaf | Node(Tree, val: int, Tree)

function method Sum(t: Tree): int {
  if t == Leaf then  // equality on datatypes
    0
  else
    var Node(left, value, right) := t;  // let with pattern
    Sum(left) + value + Sum(right)
}

method InorderPrint(t: Tree) {
  if t.Node? {  // discriminator
    var Node(left, value, right) := t;  // var with pattern
    InorderPrint(left);
    print value, " ";
    InorderPrint(right);
  }
}

module Regressions {
  method Test() {
    var a := F(2);
    var b := G(2);
    var c := H(2);
    var d := Gimmie<SoReal>();
    print a, " ", b, " ", c, " ", d, "\n"; // 12.0 15.0 15.0 15.0
  }

  function method F(xyz: int): real
  {
    // Because the following let expression is at the top level of the function
    // body, TrExprOpt is called (not TrExpr), and it converts these let variables
    // into local variables. So, this case always worked.
    var abc := 10;
    var def := xyz;
    12.0
  }

  // This one had problems:
  function method G(xyz: int): real
  {
    3.0 +
      var abc := 10;
      // The use of "xyz" in the following line was not always adequately protected.
      var def := xyz; // use of formal parameter in RHS of let inside another let
      12.0
  }

  function method H(xyz: int): real
  {
    3.0 +
      var abc := 10;
      var def := abc; // was never a problem, since this is not a formal parameter
      12.0
  }

  type SoReal = r: real | 10.0 <= r
    witness
      3.0 +
        var abc := 10;
        var def := abc; // was never a problem, since this is not a formal parameter
        12.0

  method Gimmie<T(0)>() returns (t: T) { }
}
