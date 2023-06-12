// RUN: %dafny /compile:4 /compileTarget:py "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
    var x: multiset<int> := multiset{};
    x := x[1 := 18446744073709551616];
    print |x|, "\n";
}