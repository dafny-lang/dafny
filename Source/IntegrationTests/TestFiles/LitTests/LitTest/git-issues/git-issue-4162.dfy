// NONUNIFORM: %testDafnyForEachCompiler doesn't support /out
// RUN: %run --target py --output M "%s" > "%t"
// RUN: %run --target cs --output M "%s" >> "%t"
// RUN: %run --target java --output M "%s" >> "%t"
// RUN: %run --target js --output M "%s" >> "%t"
// RUN: %run --target go --output M "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module M {
    const i := 0
}

method Main() {
    print M.i, "\n";
}
