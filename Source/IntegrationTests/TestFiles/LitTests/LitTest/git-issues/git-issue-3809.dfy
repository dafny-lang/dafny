// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" 

module m {
  datatype D = A
             | B
             | C {
    static const Default: D := B
  }

  method Main() {
    var x := D.Default;
    match x {
      case A => print "A!\n";
      case B => print "B!\n";
      case C => print "C!\n";
    }
     print "Hello!\n";
  }

}
