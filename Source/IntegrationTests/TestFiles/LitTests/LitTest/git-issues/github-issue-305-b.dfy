// RUN: %exits-with 3 %translate cs --show-snippets=false "%s" > "%t"
// RUN: %diff "%s".expect "%t"

method hasNoBody()

method Main() {
    hasNoBody();
    print "hello\n";
}
