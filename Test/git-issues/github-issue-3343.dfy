// RUN: %testDafnyForEachCompiler "%s"
method Bug() {
    var zero := 0;
    var a := new int[zero] [];
}
