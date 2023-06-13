// RUN: %baredafny run "%s" -t:java > "%t"
// RUN: %diff "%s.expect" "%t"
method Bug() {
    var zero := 0;
    var a := new int[zero] [];
}
