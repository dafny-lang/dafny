// RUN: %baredafny translate cs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
    print "hello\n";
}
