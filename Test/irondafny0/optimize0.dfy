// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment /optimize
// See https://github.com/dafny-lang/dafny/issues/508

method Main() {
    print "o hai!";
}
