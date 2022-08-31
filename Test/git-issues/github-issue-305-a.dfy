// RUN: %baredafny translate --quiet "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
    print "hello\n";
}
