// RUN: %baredafny run %args --target=cs "%s" >> "%t"

datatype T = Leaf(x: int) | T(t: T) {
  function method {:tailrecursion} TR() : int {
    if Leaf? then 0
    else t.TR()
  }
}

method Main() {
  print Leaf(0).TR(), '\n';
}
