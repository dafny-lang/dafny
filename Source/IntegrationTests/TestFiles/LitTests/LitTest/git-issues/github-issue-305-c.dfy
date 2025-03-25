// RUN: %translate cs %trargs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// At some point (https://github.com/dafny-lang/dafny/pull/307#issuecomment-510191495)
// this used to produce an executable even though it shouldn't,
// therefore we compare the output of "baredafny", which contains messages regarding
// whether an executable has been produced.

method Main() {
    print "hello\n";
}
