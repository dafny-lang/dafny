// NONUNIFORM: %testDafnyForEachCompiler doesn't support /out
// RUN: %dafny /compile:4 /compileTarget:py /out:M "%s" > "%t"
// RUN: %dafny /compile:4 /compileTarget:cs /out:M "%s" >> "%t"
// RUN: %dafny /compile:4 /compileTarget:java /out:M "%s" >> "%t"
// RUN: %dafny /compile:4 /compileTarget:js /out:M "%s" >> "%t"
// RUN: %dafny /compile:4 /compileTarget:go /out:M "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module M {
    const i := 0
}

method Main() {
    print M.i, "\n";
}
