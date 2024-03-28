// NONUNIFORM: %testDafnyForEachCompiler doesn't support /out
// RUN: %dafny /compile:4 --target py /out:M "%s" > "%t"
// RUN: %dafny /compile:4 --target cs /out:M "%s" >> "%t"
// RUN: %dafny /compile:4 --target java /out:M "%s" >> "%t"
// RUN: %dafny /compile:4 --target js /out:M "%s" >> "%t"
// RUN: %dafny /compile:4 --target go /out:M "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module M {
    const i := 0
}

method Main() {
    print M.i, "\n";
}
