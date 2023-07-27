// RUN: %testDafnyForEachCompiler "%s" -- --output:M

module M {
    const i := 0
}

method Main() {
    print M.i, "\n";
}