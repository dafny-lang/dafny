// RUN: %testDafnyForEachCompiler "%s"

method Main() {
  CallFromTextuallyAbove.Test();
  CallFromTextuallyBelow.Test();
}

class CallFromTextuallyAbove {
  static method Test() {
    var x := new Class;
    x.M();
    print x.m, "\n";
  }
}

class Class {
  const m: int := 18
  method M() {
    print "hello M, ";
  }
}

class Ssalc {
  const m: int := 19
  method M() {
    print "hi M, ";
  }
}

class CallFromTextuallyBelow {
  static method Test() {
    var x := new Ssalc;
    x.M();
    print x.m, "\n";
  }
}
