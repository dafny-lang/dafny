// RUN: %testDafnyForEachCompiler "%s"

datatype D = A(int) | C(int) {
  function Test(): D {
    match this{
      case A(_) | C(_) =>
        this
    }
  }
}
method Main() {
  var x := C(0).Test();
  print "ok";
}