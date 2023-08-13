// RUN: %dafny /compile:4 /compileTarget:py /out:M "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
    const i := 0
}

method Main() {
    print M.i, "\n";
}
