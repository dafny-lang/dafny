// RUN: %baredafny /compile:0 /spillTargetCode:2 "%s"

// At some point (https://github.com/dafny-lang/dafny/pull/307#issuecomment-509914424)
// this used to return error code 0 (success) instead of non-zero (failure).
// We tell lit that this test must fail (ie lit will fail if the test doesn't fail):
// XFAIL: *

method hasNoBody()

method Main() {
    hasNoBody();
    print "hello\n";
}
