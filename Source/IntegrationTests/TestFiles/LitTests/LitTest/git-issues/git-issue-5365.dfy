// RUN: %baredafny verify %args --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype S  = S(
    n:nat
) {
    function f():S { this }
    function g():S { this.(n := 0).f() }
}