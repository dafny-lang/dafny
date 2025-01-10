// NONUNIFORM: %testDafnyForEachCompiler doesn't support /out
// RUN: %run --target py --build M "%s" > "%t"
// RUN: %run --target cs --build M "%s" >> "%t"
// RUN: %run --target java --build M "%s" >> "%t"
// RUN: %run --target js --build M "%s" >> "%t"
// RUN: %run --target go --build M "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module M {
    const i := 0
}

method Main() {
    print M.i, "\n";
}
