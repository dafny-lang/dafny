// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

method Main() {
    var a := 0;
    for i := 0 to |(set x: int | 0 <= x < 3 :: x)| {
        a := a + 1;
    }
    print a, "\n";
}
