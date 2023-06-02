// RUN: %dafny /compile:3 /compileTarget:java /spillTargetCode:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
}
