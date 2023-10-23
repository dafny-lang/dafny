// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0
method Bug() {
    var zero := 0;
    var a := new int[zero] [];
}
