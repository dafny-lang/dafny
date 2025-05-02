// RUN: %exits-with 4 %run "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module Spec {
    method Greet(b: bool)
        requires b
}

module Impl refines Spec {
    method Greet(b: bool) {
        print "o hai!\n";
    }

    method Xyzzy(b: bool)
        requires b
    {}

    method Main() {
        Greet(true);
        Xyzzy(false);
    }
}
