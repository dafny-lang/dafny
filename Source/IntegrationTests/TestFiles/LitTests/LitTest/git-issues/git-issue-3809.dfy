// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" 

module m {
  datatype D = A
             | B
             | C {
    static const Default: D := A
  }

  method Main() {
     print "Hello!\n";
  }

}
