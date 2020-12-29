// UNSUPPORTED: windows
// RUN: %baredafny /countVerificationErrors:0 /compile:0 /spillTargetCode:2 "%s" > "%t.2"
// RUN: sed -e "s:%S:...:" -e 'sx\\x/x' < "%t.2" > "%t"
// RUN: %diff "%s".expect "%t"

method hasNoBody()

method Main() {
    hasNoBody();
    print "hello\n";
}
