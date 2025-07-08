// RUN: %baredafny test "%s" > "%t"
// RUN: %baredafny test --methods-to-test='q' "%s" >> "%t"
// RUN: %baredafny test --methods-to-test='m' "%s" >> "%t"
// RUN: %baredafny test --methods-to-test='M.*' "%s" >> "%t"
// RUN: %baredafny test --methods-to-test='^.$' "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method {:test} m() {
  print "Testing m\n";
}
method {:test} q() {
  print "Testing q\n";
}
method {:test} pp() {
  print "Testing pp\n";
}

module M {

  method {:test} m() {
    print "Testing M.m\n";
  }
  method {:test} t() {
    print "Testing M.t\n";
  }
}

