// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" 

module m {
  datatype D = A
             | B
             | C {
    static const Default: D := B // This one will be translated as Default_
    method Default_() { // Just to be sure there is no clash: this is translated as Default__
      print "Default_ Method\n";
    }
  }



  method Main() {
    var x := D.Default;
    x.Default_();
    match x {
      case A => print "A!\n";
      case B => print "B!\n";
      case C => print "C!\n";
    }
    print "Hello!\n";
  }

}
