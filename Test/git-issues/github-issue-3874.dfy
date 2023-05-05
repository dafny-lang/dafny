// RUN: %testDafnyForEachCompiler "%s"

method Main() {
    var s: multiset<bool> := multiset{true};

    while (s != multiset{}) {
        var x :| x in s;
	s := s[x := 0];
    }

    print "done", "\n";
}
