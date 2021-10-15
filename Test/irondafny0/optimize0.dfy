// RUN: %dafny /compile:3 /optimize /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// See https://github.com/dafny-lang/dafny/issues/508

method Main() {
    print "o hai!";
}
