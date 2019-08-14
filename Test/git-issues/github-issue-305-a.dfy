// RUN: %baredafny /compile:0 /spillTargetCode:2 "%s"
// This used to return exit code 3 (failure) instead of 0 (success)

method Main() {
    print "hello\n";
}
