// RUN: %testDafnyForEachCompiler "%s"

module C {
  method Test() {
    print "done\n";
  }
}

method Main(){
  C.Test();
}