// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"
method Bug() {
    var zero := 0;
    var a := new int[zero] [];
}
