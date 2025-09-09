// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

class C {
  constructor(ghost x: int)
  {
  }
}

ghost function f() : int { 0 }

method Main() {
  var c := new C(f());
}

