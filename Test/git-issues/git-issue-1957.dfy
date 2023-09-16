// RUN: %dafny /compile:0 /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class {:autocontracts} Thing {
    ghost predicate Valid() {
        true
    }
}
