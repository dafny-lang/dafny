// RUN: %dafny /compile:4 /compileTarget:cs "%s" >> "%t"

datatype T = Leaf(x: int) | T(t: T) {
  function {:tailrecursion} TR() : int {
    if Leaf? then 0
    else t.TR()
  }
}

method Main() {
  print Leaf(0).TR(), '\n';
}
