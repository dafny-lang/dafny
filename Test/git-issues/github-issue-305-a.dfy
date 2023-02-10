// RUN: %translate cs --cores:2 --use-basename-for-filename --verification-time-limit:300 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
    print "hello\n";
}
