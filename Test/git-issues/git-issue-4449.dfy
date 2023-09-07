// RUN: %testDafnyForEachCompiler "%s"

module AnyName {
  class B {
    const i := 1

    constructor() {}
  }

  class AnyName {
    const j: B

    constructor ()
    {
      this.j := new B();
    }
  }
}

method Main() {
  var b := new AnyName.B();
  var an := new AnyName.AnyName();
  print b, "\n", an, "\ndone", "\n";
}
