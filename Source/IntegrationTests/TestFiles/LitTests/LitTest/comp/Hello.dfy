// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

method Main() {
    print "Hello, World! Best, Dafny\n";
    var x := 14;
    print "x is ", x, "\n";
    var y := false;
    print "y is ", y, "\n";
}
