// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

trait Base {}
class Derived extends Base { var n: int constructor() { n := 0; } }

method f(b: Base) {
  if (b is Derived) {
    print "(b as Derived).n == ", (b as Derived).n, "\n";
  }
}

method Main() {
  var d := new Derived();
  f(d);
}
