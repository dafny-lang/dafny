// RUN: %baredafny /compile:0 /spillTargetCode:2 "%s" > "%t" || echo ERROR EXIT >> "%t"
// RUN: %diff "%s".expect "%t"

method hasNoBody()

method Main() {
    hasNoBody();
    print "hello\n";
}
