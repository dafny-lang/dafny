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
