// RUN: %dafny /countVerificationErrors:0 /compile:0 /spillTargetCode:2 /useBaseNameForFileName "%s" > "%t"
// RUN: %diff "%s".expect "%t"

method hasNoBody()

method Main() {
    hasNoBody();
    print "hello\n";
}
