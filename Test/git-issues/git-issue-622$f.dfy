// RUN: %baredafny run %args --target=java "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
}
