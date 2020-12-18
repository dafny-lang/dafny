// RUN: %baredafny /compile:0 /spillTargetCode:2 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
    print "hello\n";
}
