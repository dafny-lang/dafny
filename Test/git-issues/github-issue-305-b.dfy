// RUN: %baredafny /countVerificationErrors:0 /compile:0 /spillTargetCode:2 "%s" > "%t"
// RUN: sed -e "s:%S:...:" -e 'sx\\x/x' < "%t" > "%t".2
// RUN: %diff "%s.expect" "%t".2

method hasNoBody()

method Main() {
    hasNoBody();
    print "hello\n";
}
