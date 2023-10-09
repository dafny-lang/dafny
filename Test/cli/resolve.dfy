// RUN: %baredafny resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() ensures false {
}