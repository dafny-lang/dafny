// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

method Main() {
    var x: multiset<int> := multiset{};
    x := x[1 := 18446744073709551616];
    print |x|, "\n";
}
