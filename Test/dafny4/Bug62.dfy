// RUN: %exits-with 3 %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  constructor C() { }
  method Main()  // not Main since the enclosing class has a constructor.
  {
    print "hello, I'm running ... in C\n";
  }
}

class D {
  method Main()  // not Main since it has modifies clause.
   modifies this;
  {
    print "hello, I'm running ... in D\n";
  }
}


class E {
  static method Main()  // not Main since it has requires clause.
   requires true;
  {
    print "hello, I'm running ... in E\n";
  }
}
